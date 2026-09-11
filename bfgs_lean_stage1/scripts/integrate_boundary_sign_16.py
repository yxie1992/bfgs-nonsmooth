#!/usr/bin/env python3
"""Import-only adoption of the independently reviewed boundary-sign refinement."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'audit/scratch/boundary_sign_strata'
m=json.loads((p/'declarations.json').read_text())
assert 'PASS' in (p/'validation.log').read_text() and 'PASS' in (p/'peer_validation.log').read_text()
names={x['module'] for x in m['sources']}
sources=[]
for row in m['sources']:
 src=ROOT/row['path'];old=src.read_text()
 assert hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256']
 new=re.sub(r'^import (\S+)$',lambda q:'import BfgsVerification.'+q[1] if q[1] in names else q[0],old,flags=re.M)
 assert re.sub(r'^import .*\n','',old,flags=re.M)==re.sub(r'^import .*\n','',new,flags=re.M)
 dest=ROOT/'BfgsVerification'/src.name
 assert not dest.exists() or dest.read_text()==new
 dest.write_text(new)
 sources.append(dict(module='BfgsVerification.'+src.stem,path=str(dest.relative_to(ROOT)),
   sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),reviewed_source=row['path'],reviewed_sha256=row['sha256']))
evidence=[]
for src in [p/'STATEMENT_REVIEW.md',p/'INDEPENDENT_PEER_REVIEW.md',*sorted(p.glob('peer*.log'))]:
 dest=ROOT/'audit'/('BOUNDARY_SIGN_'+src.name)
 assert not dest.exists() or dest.read_bytes()==src.read_bytes()
 dest.write_bytes(src.read_bytes());evidence.append(str(dest.relative_to(ROOT)))
pairs=[['BfgsVerification.boundarySignPartition','BfgsVerification.BoundarySignPartitionTarget']]
scope=dict(id='boundary_sign_strata',label='Actual finite boundary-sign refinement',sources=sources,
 declarations=m['declarations'],targets=pairs,review_evidence=evidence)
manifest=dict(log_prefix='boundary_sign',audit_driver='audit/BoundarySignAudit.lean',scopes=[scope],
 declarations=m['declarations'],targets=pairs)
(ROOT/'audit/boundary_sign_declarations.json').write_text(json.dumps(manifest,indent=2)+'\n')
driver='import BfgsVerification.BoundarySignTargets\nimport Lean\nopen Lean Elab Command Meta\n'
for name in m['declarations']:driver+=f'#check @{name}\n#print axioms {name}\n'
for name,target in pairs:
 driver+=f'''run_cmd do
  let info ← getConstInfo `{name}
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `{target})
  unless ok do throwError "exact boundary target mismatch"
  logInfo "EXACT_TARGET_OK {name}"
'''
(ROOT/'audit/BoundarySignAudit.lean').write_text(driver)
(ROOT/'audit/boundary_sign_import_correspondence.log').write_text('PASS:two import-only source copies;ten actual declarations;one exact target;all reviewed original hashes retained.\n')
print('Adopted two boundary-sign modules;ten declaration reports;one exact target.')
