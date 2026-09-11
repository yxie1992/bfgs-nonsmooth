#!/usr/bin/env python3
"""Adopt reviewed general projection and actual affine-critical definability."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
config=[('semialgebraic_queries','GENERAL_PROJECTION',[
 ('rationalIndexParameter','RationalIndexParameterTarget'),
 ('tarskiQueryParameter','TarskiQueryParameterTarget'),
 ('simultaneousPolynomialProjection','SimultaneousPolynomialProjectionTarget'),
 ('booleanScalarProjection','BooleanScalarProjectionTarget'),
 ('generalCoordinateProjection','GeneralCoordinateProjectionTarget')]),
 ('affine_critical_definability','AFFINE_CRITICAL_DEFINABILITY',[
 ('affineCriticalSemialgebraic','AffineCriticalSemialgebraicTarget')])]
scopes=[]
for folder,label,targets in config:
 b=ROOT/'audit/scratch'/folder
 for f in ['validation.log','peer_validation.log']:assert 'PASS' in (b/f).read_text(),f
 m=json.loads((b/'declarations.json').read_text())
 scopes.append(dict(id=folder,label=label,sources=m['sources'],declarations=m['declarations'],targets=[['BfgsVerification.'+a,'BfgsVerification.'+c] for a,c in targets]))
mods={f.stem for f in (ROOT/'BfgsVerification').glob('*.lean')}|{Path(s['path']).stem for scope in scopes for s in scope['sources']}
def normalize(s):
 return re.sub(r'^import ([A-Za-z0-9_]+)$',lambda m:'import BfgsVerification.'+m[1] if m[1] in mods else m[0],s,flags=re.M)
for scope in scopes:
 rows=[];b=ROOT/'audit/scratch'/scope['id']
 for r in scope['sources']:
  p=ROOT/r['path'];raw=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  out=normalize(raw);assert re.sub(r'^import .*\n','',raw,flags=re.M)==re.sub(r'^import .*\n','',out,flags=re.M)
  d=ROOT/'BfgsVerification'/p.name;assert not d.exists();d.write_text(out)
  rows.append(dict(module='BfgsVerification.'+p.stem,path=str(d.relative_to(ROOT)),sha256=hashlib.sha256(d.read_bytes()).hexdigest(),reviewed_source=r['path'],reviewed_sha256=r['sha256']))
 scope['sources']=rows;evidence=[]
 for f in ['STATEMENT_REVIEW.md','INDEPENDENT_PEER_REVIEW.md','peer_validation.log','peer_axioms_contracts.log']:
  d=ROOT/'audit'/(scope['label']+'_'+f);assert not d.exists();d.write_bytes((b/f).read_bytes());evidence.append(str(d.relative_to(ROOT)))
 scope['review_evidence']=evidence
names=[n for scope in scopes for n in scope['declarations']];pairs=[p for scope in scopes for p in scope['targets']]
assert len(names)==66 and len(pairs)==6
m=dict(scopes=scopes,declarations=names,targets=pairs,audit_driver='audit/SemialgebraicProjectionAudit.lean',log_prefix='semialgebraic_projection')
(ROOT/'audit/semialgebraic_projection_declarations.json').write_text(json.dumps(m,indent=2)+'\n')
s=''.join('import '+r['module']+'\n' for scope in scopes for r in scope['sources'])+'set_option pp.universes true\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
s+='open Lean Elab Command in\nrun_cmd do\n  for (decl,target) in [\n'
s+='\n'.join('    (`'+a+', `'+b+')'+(',' if i+1<len(pairs) else '] do') for i,(a,b) in enumerate(pairs))+'\n'
s+='''    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "target mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
'''
(ROOT/'audit/SemialgebraicProjectionAudit.lean').write_text(s)
(ROOT/'audit/semialgebraic_projection_import_correspondence.log').write_text('PASS: ten frozen owned source hashes matched; only imports qualified;66 actual declarations and six targets retained. General projection plus actual critical-set definability; finite smooth paths remain open.\n')
print('Adopted ten files/66 declaration reports/six targets; full central audit pending.')
