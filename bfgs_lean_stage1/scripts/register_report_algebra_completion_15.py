#!/usr/bin/env python3
"""Register the independently reviewed fifteenth milestone and freeze Lean sources."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
manifests=['sign_query','positive_index','d_source_supplement','semialgebraic_projection']
pairs=[]
for name in manifests:
 m=json.loads((ROOT/f'audit/{name}_declarations.json').read_text())
 assert 'PASS' in (ROOT/f'audit/{name}_validation.log').read_text(),name
 pairs+=m['targets']
 for scope in m['scopes']:
  for row in scope['sources']:
   assert hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256']
assert len(pairs)==27 and len({a for a,b in pairs})==27
p=ROOT/'scripts/check.py';code=p.read_text();assert 'REPORT_ALGEBRA_COMPLETION_TARGETS' not in code
block='REPORT_ALGEBRA_COMPLETION_TARGETS = {\n'
for a,b in pairs:
 flag=a.removeprefix('BfgsVerification.').replace('.','_')+'_verified'
 block+=f'    "{flag}":\n        ("{a}", "{b}"),\n'
block+='}\n'
code=code.replace('ALL_TARGETS = ',block+'ALL_TARGETS = ',1)
code=code.replace('| REPORT_GEOMETRY_COMPLETION_TARGETS\n','| REPORT_GEOMETRY_COMPLETION_TARGETS | REPORT_ALGEBRA_COMPLETION_TARGETS\n',1)
code=code.replace('MODULE_M_AND_REPORT_GEOMETRY_COMPLETION_TARGETS_VERIFIED','MODULE_M_AND_REPORT_ALGEBRA_COMPLETION_TARGETS_VERIFIED')
old='A general nonlinear Boolean semialgebraic projection/path/critical-value closure and the dependent C semialgebraic alternative; final source/synthesis/evidence reconciliation. Actual C arbitrary-dimensional constant-rank C1 field/secant theorem, L Jacobian precision, two-piece termination and arbitrary-dimensional no-infinite-continuation, and A multiplicity/quadratic-projection/positive-pseudo-division infrastructure are now checked. The finite polynomial fragments do not prove general quantifier elimination; see REPORT_STATUS.json'
new='A finite semialgebraic smooth path/component decomposition and critical-value closure, with the dependent C semialgebraic alternative; D literal non-strict-interpreter and immediate finite-algebra corollary wrappers; final source/synthesis and historical evidence reconciliation. General arbitrary-degree Boolean/finite-coordinate semialgebraic projection and actual supporting/affine-critical graph definability are now proved, together with actual root-sign/Euclidean-index computation. D actual numerical precision, original-box update denominators and exact Euclidean nine-query bound, H actual recurrent-cardinality sharpness and I actual ridge supersession are checked; see REPORT_STATUS.json'
assert old in code;code=code.replace(old,new)
anchor='("BfgsVerification.LocalStableOrbit.stableOrbit", "Actual strict derivative'
addition='''("BfgsVerification.RealAlgebraicGeometry.supportGraph_semialgebraic_of_projection", "Explicit projection premise in this reusable bridge is now discharged by actual general coordinate projection in supportGraph_semialgebraic"),
                ("BfgsVerification.AffineSupportPath.finite_values_of_finite_path_cover", "Finite actual affine-critical path cover is explicit and remains to be derived from semialgebraicity"),
                ("BfgsVerification.AffineSupportPath.low_level_affine_correct_of_finite_values", "Finite actual affine-critical value set is explicit; the general semialgebraic finite-value application remains pending"),
                '''
assert anchor in code;code=code.replace(anchor,addition+anchor,1);p.write_text(code)
p=ROOT/'BfgsVerification.lean';old=p.read_text();comment=old[old.index('/-!'):]
modules=sorted((ROOT/'BfgsVerification').glob('*.lean'));assert len(modules)==631,len(modules)
p.write_text(''.join('import BfgsVerification.'+f.stem+'\n' for f in modules)+'\n'+comment)
p=ROOT/'Audit.lean';old=p.read_text();marker='/- Fifteenth milestone: actual general semialgebraic projection, critical-set definability, and source precision/corollaries. -/'
assert marker not in old
text='\n'+marker+'\n'
for a,b in pairs:text+=f'#print {b}\nexample : {b} := {a}\n#print axioms {a}\n'
p.write_text(old+text)
(ROOT/'audit/report_algebra_completion_targets.json').write_text(json.dumps(pairs,indent=2)+'\n')
sources=modules+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean']
hashes={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(sources)}
(ROOT/'audit/report_algebra_completion_source_hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(f'Registered27 new exact targets,205 total; froze{len(sources)} Lean files. Full pinned audit pending.')
