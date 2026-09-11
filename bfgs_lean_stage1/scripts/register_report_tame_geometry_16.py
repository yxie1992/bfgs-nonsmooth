#!/usr/bin/env python3
"""Register reviewed milestone16 targets and freeze the actual Lean sources."""
import ast,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
pairs=[];sources=[]
for name in ['tame_geometry','d_literal_closure','boundary_sign','general_smooth_cover','critical_geometry']:
 m=json.loads((ROOT/f'audit/{name}_declarations.json').read_text())
 assert 'PASS' in (ROOT/f'audit/{name}_validation.log').read_text(),name
 pairs+=m['targets'];sources += [r for scope in m['scopes'] for r in scope['sources']]
for name,prefix,theorem,target in [('smooth_path_components','smooth_components','finiteSmoothComponents','FiniteSmoothComponentsTarget'),('semialgebraic_smooth_components','semialgebraic_smooth_components','semialgebraicSmoothComponents','SemialgebraicSmoothComponentsTarget')]:
 m=json.loads((ROOT/f'audit/{name}_declarations.json').read_text())
 assert 'PASS' in (ROOT/f'audit/{prefix}_validation.log').read_text(),name
 assert m['targets']==['BfgsVerification.'+target]
 pairs.append(['BfgsVerification.'+theorem,'BfgsVerification.'+target]);sources += m['sources']
assert len(pairs)==28 and len({a for a,b in pairs})==28
assert len(sources)==60 and len({r['path'] for r in sources})==60
for row in sources:assert hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
p=ROOT/'scripts/check.py';code=p.read_text();assert 'REPORT_TAME_GEOMETRY_TARGETS' not in code
block='REPORT_TAME_GEOMETRY_TARGETS = {\n'
for a,b in pairs:
 flag=a.removeprefix('BfgsVerification.').replace('.','_')+'_verified'
 block+=f'    "{flag}":\n        ("{a}", "{b}"),\n'
block+='}\n'
code=code.replace('ALL_TARGETS = ',block+'ALL_TARGETS = ',1)
code=code.replace('| REPORT_ALGEBRA_COMPLETION_TARGETS\n','| REPORT_ALGEBRA_COMPLETION_TARGETS | REPORT_TAME_GEOMETRY_TARGETS\n',1)
code=code.replace('MODULE_M_AND_REPORT_ALGEBRA_COMPLETION_TARGETS_VERIFIED','MODULE_M_AND_REPORT_TAME_GEOMETRY_TARGETS_VERIFIED')
code=code.replace('Finite actual affine-critical path cover is explicit and remains to be derived from semialgebraicity','Finite actual affine-critical path cover remains explicit in this reusable implication; the actual general finite-value conclusion is now proved by semialgebraic_affine_critical_values using the constructed smooth cover of the lifted critical graph')
code=code.replace('Finite actual affine-critical value set is explicit; the general semialgebraic finite-value application remains pending','Finite actual affine-critical value set is explicit in this reusable implication; discharged from actual convex semialgebraicity by semialgebraic_affine_critical_values and semialgebraic_low_affine_critical_gap')
anchor='("BfgsVerification.LocalStableOrbit.stableOrbit", "Actual strict derivative'
addition='''("BfgsVerification.RealAlgebraicGeometry.finite_critical_values_of_smooth_graph_cover", "Actual finite smooth critical-graph cover; constructed from genuine semialgebraicity in semialgebraic_affine_critical_values"),
                ("BfgsVerification.RealAlgebraicGeometry.planar_low_basin_of_finite_critical_values", "Actual finite critical-value image; discharged in semialgebraic_planar_low_basin, with the source compactness/strict-contour/local-regularity hypotheses retained"),
                ("BfgsVerification.RealAlgebraicGeometry.finite_semialgebraic_smooth_components", "Finite semialgebraic smooth cover; constructed from genuine semialgebraicity in semialgebraic_smooth_components"),
                '''
assert anchor in code;code=code.replace(anchor,addition+anchor,1)
start=code.index('            "A finite semialgebraic smooth path/component decomposition',code.index('status["outside_verified_scope"]'))
end=code.index('\n',start)
code=code[:start]+'            "The literal A assertion that witnessing path graphs are semialgebraic remains under separate verification. The actual general finite smooth cover, finite ordinary/actual smooth-path components, finite critical values, original low gap and C tame basins are now proved. D literal non-strict interpreter and finite-algebra identities are also proved. Historical E jobs/counts/timings/archive identity and the old R four-piece attribution remain unverified because original inputs are absent. See REPORT_STATUS.json",'+code[end:]
parsed=ast.parse(code);targets={}
for node in parsed.body:
 if isinstance(node,ast.Assign) and isinstance(node.value,ast.Dict) and any(isinstance(t,ast.Name) and (t.id=='TARGETS' or t.id.endswith('_TARGETS')) for t in node.targets):
  targets.update(ast.literal_eval(node.value))
assert len(targets)==233,len(targets)
p.write_text(code)
p=ROOT/'BfgsVerification.lean';old=p.read_text();comment=old[old.index('/-!'):]
modules=sorted((ROOT/'BfgsVerification').glob('*.lean'));assert len(modules)==691,len(modules)
p.write_text(''.join('import BfgsVerification.'+f.stem+'\n' for f in modules)+'\n'+comment)
p=ROOT/'Audit.lean';old=p.read_text();marker='/- Sixteenth milestone: actual finite smooth geometry, critical values, low gaps and planar basins; literal D closure. -/'
assert marker not in old
text='\n'+marker+'\n'
for a,b in pairs:text+=f'#print {b}\nexample : {b} := {a}\n#print axioms {a}\n'
p.write_text(old+text)
(ROOT/'audit/report_tame_geometry_targets.json').write_text(json.dumps(pairs,indent=2)+'\n')
files=modules+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean']
hashes={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(files)}
(ROOT/'audit/report_tame_geometry_source_hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('Registered28 new exact targets,233 total; froze693 Lean files. Full pinned audit pending.')
