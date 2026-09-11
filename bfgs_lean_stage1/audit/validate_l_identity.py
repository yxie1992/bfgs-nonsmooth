import hashlib,json,re
from pathlib import Path
base=Path(__file__).resolve().parent
root=base.parent
m=json.loads((base/'l_identity_declarations.json').read_text())
for s in m['sources']:
 p=root/s['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==s['sha256'],p
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',p.read_text()),p

build=(base/'l_identity_build.log').read_text();assert 'Build completed successfully.' in build and 'error:' not in build
s=(base/'l_identity_axioms.log').read_text();assert 'error:' not in s
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s)
assert {n for n,a in reports}==set(m['declarations'])
for n,a in reports:assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},(n,a)
for th,tg in m['targets']:assert f'EXACT_TARGET_OK {th} {tg}' in s
print(f"PASS: {len(m['sources'])} frozen sources; {len(m['declarations'])} actual type/transitive-axiom reports; {len(m['targets'])} exact targets; fresh compiler evidence.")
