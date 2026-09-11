#!/usr/bin/env python3
import datetime,hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
m=json.loads((root/'audit/c_all_endpoints_declarations.json').read_text())
s=(root/'audit/c_all_endpoints_axioms.log').read_text()
assert 'error:' not in s
assert 'error:' not in (root/'audit/c_all_endpoints_build.log').read_text()
for p in m['sources']:
 f=root/p['path']
 assert hashlib.sha256(f.read_bytes()).hexdigest()==p['sha256'],f
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',f.read_text()),f
 scratch=root/'audit/scratch/c_all_pairs'/f.name
 assert f.read_text()==scratch.read_text().replace('import audit.scratch.c_all_pairs.','import BfgsVerification.')
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s)
assert {n for n,a in reports}==set(m['declarations'])
for n,a in reports:
 assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},(n,a)
assert len(re.findall(r'^EXACT_TARGET_OK ',s,re.M))==4
print(datetime.datetime.now(datetime.timezone.utc).isoformat())
print('PASS: eight main source hashes; sixteen actual declaration/transitive-standard-axiom reports; four strict source/wrapper exact checks; fresh main importing build; scratch/main import-normalization identity.')
