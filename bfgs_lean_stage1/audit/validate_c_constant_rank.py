#!/usr/bin/env python3
import datetime,hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
base=root/'audit'
m=json.loads((base/'c_constant_rank_declarations.json').read_text())
s=(base/'c_constant_rank_axioms.log').read_text()
assert 'error:' not in s
assert 'error:' not in (base/'c_constant_rank_build.log').read_text()
for item in m['sources']:
 f=root/item['path']
 assert hashlib.sha256(f.read_bytes()).hexdigest()==item['sha256'],f
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',f.read_text()),f
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s)
assert len(reports)==len(m['declarations'])
assert {n for n,_ in reports}==set(m['declarations'])
for n,a in reports:
 assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},(n,a)
assert len(re.findall(r'^EXACT_TARGET_OK ',s,re.M))==4
print(datetime.datetime.now(datetime.timezone.utc).isoformat())
print(f'PASS: {len(m["explicit_declarations"])} explicit declarations, {len(m["generated_structure_declarations"])} structure constructors/projections, {len(m["declarations"])} standard-axiom reports, {len(m["sources"])} frozen delivered source hashes, four strict source/wrapper contracts, main compiler build.')
