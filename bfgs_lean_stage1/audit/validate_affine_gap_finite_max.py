from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parent.parent
assert 'Build completed successfully.' in (root/'audit/affine_gap_finite_max_build.log').read_text()
for prefix,targets in [('a_affine_gap',1),('c_finite_max',2)]:
 modules=json.loads((root/f'audit/{prefix}_declarations.json').read_text())['modules']
 names=[d['name'] for x in modules for d in x['declarations']]
 reports=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(root/f'audit/{prefix}_axioms.log').read_text()))
 assert set(names)==set(reports),(set(names)-set(reports),set(reports)-set(names))
 for name,axioms in reports.items():
  assert set(axioms.replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 for module in modules:
  source=root/module['file']
  assert hashlib.sha256(source.read_bytes()).hexdigest()==module['sha256'],source
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source.read_text()),source
 assert (root/f'audit/{prefix}_contracts.log').read_text().count('EXACT_TARGET_OK ')==targets
 text=f'PASS: delivered main pinned Lake build; {len(modules)} modules/{len(names)} explicit declarations; complete actual types and standard transitive axioms; {targets} strict exact-target checks; all {len(modules)} frozen main hashes unchanged. Reproduction uses delivered main sources/manifests/audit drivers only.\n'
 (root/f'audit/{prefix}_validation.log').write_text(text)
 print(prefix+': '+text,end='')
