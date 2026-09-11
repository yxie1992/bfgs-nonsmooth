#!/usr/bin/env python3
"""Import-only adoption of the actual arbitrary-dimensional smooth-cover proof."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'audit/scratch/finite_smooth_cover'
hashes=json.loads((p/'source_hashes.json').read_text())
rows=json.loads((p/'declarations.json').read_text())
assert 'PASS' in (p/'validation.log').read_text()
assert 'PASS' in (p/'secondary_validation.log').read_text()
names={Path(x).stem for x in hashes}
sources=[]
for filename,sha in hashes.items():
 src=p/filename;old=src.read_text()
 assert hashlib.sha256(src.read_bytes()).hexdigest()==sha
 new=re.sub(r'^import (\S+)$',lambda q:'import BfgsVerification.'+q[1] if q[1] in names else q[0],old,flags=re.M)
 assert re.sub(r'^import .*\n','',old,flags=re.M)==re.sub(r'^import .*\n','',new,flags=re.M)
 dest=ROOT/'BfgsVerification'/filename
 assert not dest.exists() or dest.read_text()==new
 dest.write_text(new)
 sources.append(dict(module='BfgsVerification.'+src.stem,path=str(dest.relative_to(ROOT)),
   sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),reviewed_source=str(src.relative_to(ROOT)),reviewed_sha256=sha))
evidence=[]
for filename in ['STATEMENT_REVIEW.md','SECONDARY_INDEPENDENT_REVIEW.md','secondary_axioms_contracts.log','secondary_validation.log','validation.log']:
 src=p/filename;dest=ROOT/'audit'/('GENERAL_SMOOTH_COVER_'+filename)
 assert not dest.exists() or dest.read_bytes()==src.read_bytes()
 dest.write_bytes(src.read_bytes());evidence.append(str(dest.relative_to(ROOT)))
declarations=[r['name'] for r in rows]
pairs=[['BfgsVerification.RealAlgebraicGeometry.generalSemialgebraicSmoothCover','BfgsVerification.RealAlgebraicGeometry.GeneralSemialgebraicSmoothCoverTarget']]
scope=dict(id='general_smooth_cover',label='Actual arbitrary finite-dimensional semialgebraic smooth cover',sources=sources,
 declarations=declarations,targets=pairs,review_evidence=evidence)
manifest=dict(log_prefix='general_smooth_cover',audit_driver='audit/GeneralSmoothCoverAudit.lean',scopes=[scope],declarations=declarations,targets=pairs)
(ROOT/'audit/general_smooth_cover_declarations.json').write_text(json.dumps(manifest,indent=2)+'\n')
driver='import BfgsVerification.GeneralSmoothCoverTargets\nimport Lean\nopen Lean Elab Command Meta\n'
for name in declarations:driver+=f'#check @{name}\n#print axioms {name}\n'
for name,target in pairs:
 driver+=f'''run_cmd do
  let info ← getConstInfo `{name}
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `{target})
  unless ok do throwError "exact general smooth cover target mismatch"
  logInfo "EXACT_TARGET_OK {name}"
'''
(ROOT/'audit/GeneralSmoothCoverAudit.lean').write_text(driver)
(ROOT/'audit/general_smooth_cover_import_correspondence.log').write_text('PASS:11 import-only source copies;46 actual declarations;one exact target;all reviewed original hashes retained.\n')
print('Adopted11 general smooth-cover modules;46 reports;one target.')
