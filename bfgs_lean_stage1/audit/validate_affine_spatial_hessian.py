from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent.parent
assert 'Build completed successfully.' in (root/'audit/affine_spatial_hessian_build.log').read_text()
for scope in json.loads((root/'audit/affine_spatial_hessian_scopes.json').read_text()):
    prefix=scope['prefix']
    modules=json.loads((root/f'audit/{prefix}_declarations.json').read_text())['modules']
    names={d['name'] for m in modules for d in m['declarations']}
    reports=dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",(root/f'audit/{prefix}_axioms.log').read_text()))
    assert names==set(reports),(prefix,names-set(reports),set(reports)-names)
    for name,axioms in reports.items():
        assert set(axioms.replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    for module in modules:
        source=root/module['file']
        assert hashlib.sha256(source.read_bytes()).hexdigest()==module['sha256'],source
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source.read_text()),source
        assert not re.search(r'^import (?!BfgsVerification\.|Mathlib\.)',source.read_text(),re.M),source
    count=(root/f'audit/{prefix}_contracts.log').read_text().count(scope['marker']+' ')
    assert count==scope['contracts'],(prefix,count)
    result=f"PASS: delivered pinned Lake build; {len(modules)} frozen main sources; {len(names)} complete declaration/type/standard-transitive-axiom reports; {count} strict contracts; source hashes unchanged. Reproduction uses delivered main files only.\n"
    (root/f'audit/{prefix}_validation.log').write_text(result)
    print(prefix+': '+result,end='')
