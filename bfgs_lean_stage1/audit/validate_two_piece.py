import hashlib,json,re
from pathlib import Path
base=Path(__file__).resolve().parent
root=base.parent
m=json.loads((base/'two_piece_declarations.json').read_text())
for s in m['sources']:
    p=root/s['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==s['sha256'],p
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',p.read_text()),p
build=(base/'two_piece_build.log').read_text()
assert 'Build completed successfully.' in build and 'error:' not in build
log=(base/'two_piece_axioms.log').read_text()
assert 'error:' not in log
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
assert len(reports)==len(m['declarations'])
assert {n for n,a in reports}==set(m['declarations'])
for n,a in reports:
    assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},(n,a)
for n,t in m['targets']:
    assert f'EXACT_TARGET_OK {n} {t}' in log
print(f"PASS: {len(m['sources'])} frozen main sources, {len(m['declarations'])} actual type/standard-transitive-axiom reports, {len(m['targets'])} strict exact targets; pinned importing build; delivered-only reproduction.")
