#!/usr/bin/env python3
import datetime,hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
m=json.loads((root/'audit/semialgebraic_smooth_components_declarations.json').read_text())
for d in m['sources']:
 p=root/d['path'];s=p.read_text()
 assert hashlib.sha256(p.read_bytes()).hexdigest()==d['sha256'],p
 original=s
 for r in d['import_normalizations']:
  delivered='import '+r['delivered']+'\n'
  reviewed='import '+r['original']+'\n'
  assert original.count(delivered)==1,(p,delivered)
  original=original.replace(delivered,reviewed)
 assert hashlib.sha256(original.encode()).hexdigest()==d['reviewed_original_sha256'],p
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',s),p
for p,h in m['delivered_peer_artifacts'].items():
 assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
s=(root/'audit/semialgebraic_smooth_components_axioms_contracts.log').read_text()
assert 'error:' not in s
assert 'error:' not in (root/'audit/semialgebraic_smooth_components_build.log').read_text()
rs=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s)
assert len(rs)==len(m['declarations']) and {n for n,_ in rs}==set(m['declarations'])
for n,a in rs:assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},(n,a)
assert len(re.findall(r'^EXACT_TARGET_OK ',s,re.M))==m['strict_checks']
print(datetime.datetime.now(datetime.timezone.utc).isoformat())
print(f"PASS: {len(m['sources'])} delivered source hashes and reconstructed reviewed original hashes; {len(m['delivered_peer_artifacts'])} hashed public peer artifacts; {len(m['declarations'])} actual type/standard-axiom reports; {m['strict_checks']} strict source/wrapper checks. No excluded artifact reads.")
