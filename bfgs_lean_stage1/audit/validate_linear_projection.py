from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent.parent
prefix='a_linear_projection'
modules=json.loads((root/f'audit/{prefix}_declarations.json').read_text())['modules']
names={d['name'] for m in modules for d in m['declarations']}
reports=dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",(root/f'audit/{prefix}_axioms.log').read_text()))
assert names==set(reports),(names-set(reports),set(reports)-names)
for name,axioms in reports.items():
    assert set(axioms.replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'},(name,axioms)
for module in modules:
    source=root/module['file']
    assert hashlib.sha256(source.read_bytes()).hexdigest()==module['sha256'],source
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',source.read_text()),source
    assert not re.search(r'^import (?!BfgsVerification\.|Mathlib\.)',source.read_text(),re.M),source
assert 'Build completed successfully.' in (root/f'audit/{prefix}_build.log').read_text()
assert (root/f'audit/{prefix}_contracts.log').read_text().count('EXACT_TARGET_OK ')==3
print(f'PASS: pinned main build; {len(modules)} frozen main sources; {len(names)} complete actual types/standard-transitive-axiom reports; three strict affine-elimination contracts; all main hashes unchanged. Reproduction uses delivered main files only.')
