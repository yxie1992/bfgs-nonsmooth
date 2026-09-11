#!/usr/bin/env python3
"""Adopt reviewed actual affine-critical geometry and planar tame basins."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'audit/scratch/critical_geometry_completion'
a=ROOT/'audit/scratch/affine_critical_definability'
assert 'PASS' in (p/'final_validation.log').read_text()
assert 'PASS' in (p/'actual_critical_peer_validation.log').read_text()
for base,name in [(a,'connected_peer_validation.log'),(p,'component_peer_validation.log'),(p,'graph_values_peer_validation.log'),(p,'planar_finite_peer_validation.log')]:
 assert 'PASS' in (base/name).read_text(),name
hashes=json.loads((p/'final_source_hashes.json').read_text())
hashes.update(json.loads((a/'connected_peer_source_hashes.json').read_text())['sources'])
for name in ['component_peer_source_hashes.json','graph_values_peer_source_hashes.json','planar_finite_peer_all_hashes.json']:
 hashes.update(json.loads((p/name).read_text()))
files=[a/'ConnectedCriticalValues.lean']+[p/(n+'.lean') for n in ['SemialgebraicComponents','FiniteCriticalGraphValues','PlanarFiniteValueBasin','SemialgebraicCriticalGeometry','SemialgebraicCriticalTargets']]
names={f.stem for f in files}|{'SmoothObjectiveGraphPaths','SemialgebraicSmoothCover'}
sources=[];declarations=[]
for src in files:
 old=src.read_text();relative=str(src.relative_to(ROOT));sha=hashes[relative]
 assert hashlib.sha256(src.read_bytes()).hexdigest()==sha
 new=re.sub(r'^import (\S+)$',lambda q:'import BfgsVerification.'+q[1] if q[1] in names else q[0],old,flags=re.M)
 assert re.sub(r'^import .*\n','',old,flags=re.M)==re.sub(r'^import .*\n','',new,flags=re.M)
 dest=ROOT/'BfgsVerification'/src.name
 assert not dest.exists() or dest.read_text()==new
 dest.write_text(new)
 sources.append(dict(module='BfgsVerification.'+src.stem,path=str(dest.relative_to(ROOT)),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),reviewed_source=relative,reviewed_sha256=sha))
 namespace='BfgsVerification.AffineSupportPath.' if src.stem=='ConnectedCriticalValues' else 'BfgsVerification.' if src.stem=='SemialgebraicCriticalTargets' else 'BfgsVerification.RealAlgebraicGeometry.'
 declarations += [namespace+n for n in re.findall(r'^(?:theorem|def) (\S+)',old,re.M)]
assert len(declarations)==23 and len(set(declarations))==23
pairs=json.loads((p/'final_declarations.json').read_text())['targets']
evidence=[]
for base,filenames in [(a,['CONNECTED_VALUES_INDEPENDENT_PEER_REVIEW.md','connected_peer_axioms_contracts.log','connected_peer_validation.log']),
 (p,['COMPONENTS_INDEPENDENT_PEER_REVIEW.md','GRAPH_VALUES_INDEPENDENT_PEER_REVIEW.md','PLANAR_FINITE_INDEPENDENT_PEER_REVIEW.md','ACTUAL_CRITICAL_INDEPENDENT_PEER_REVIEW.md','component_peer_axioms_contracts.log','component_peer_validation.log','graph_values_peer_axioms_contracts.log','graph_values_peer_validation.log','planar_finite_peer_axioms_contracts.log','planar_finite_peer_validation.log','actual_critical_peer_axioms_contracts.log','actual_critical_peer_validation.log'])]:
 for filename in filenames:
  src=base/filename;dest=ROOT/'audit'/('CRITICAL_GEOMETRY_'+filename)
  assert not dest.exists() or dest.read_bytes()==src.read_bytes()
  dest.write_bytes(src.read_bytes());evidence.append(str(dest.relative_to(ROOT)))
scope=dict(id='critical_geometry',label='Actual finite critical values, ordinary components, low gap and planar tame basins',sources=sources,declarations=declarations,targets=pairs,review_evidence=evidence)
manifest=dict(log_prefix='critical_geometry',audit_driver='audit/CriticalGeometryAudit.lean',scopes=[scope],declarations=declarations,targets=pairs)
(ROOT/'audit/critical_geometry_declarations.json').write_text(json.dumps(manifest,indent=2)+'\n')
driver='import BfgsVerification.SemialgebraicCriticalTargets\nimport Lean\nopen Lean Elab Command Meta\n'
for name in declarations:driver+=f'#check @{name}\n#print axioms {name}\n'
for name,target in pairs:
 driver+=f'''run_cmd do
  let info ← getConstInfo `{name}
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `{target})
  unless ok do throwError "exact critical geometry target mismatch"
  logInfo "EXACT_TARGET_OK {name}"
'''
(ROOT/'audit/CriticalGeometryAudit.lean').write_text(driver)
(ROOT/'audit/critical_geometry_import_correspondence.log').write_text('PASS:six import-only source copies;23 actual declarations;three exact targets;all independently reviewed original source hashes preserved.\n')
print('Adopted six critical-geometry modules;23 reports;three targets.')
