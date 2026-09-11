#!/usr/bin/env python3
import datetime,hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
m=json.loads((root/'audit/l_global_targets_declarations.json').read_text())
p=root/'BfgsVerification/LGlobalTargets.lean'
assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
s=(root/'audit/l_global_targets_axioms.log').read_text()
assert 'error:' not in s
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s)
assert {n for n,a in reports}==set(m['names'])
for n,a in reports:
 assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'}
assert len(re.findall(r'^EXACT_TARGET_OK ',s,re.M))==6
assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',p.read_text())
print(datetime.datetime.now(datetime.timezone.utc).isoformat())
print('PASS: six declarations and standard-axiom reports; six exact target/type comparisons including original source theorem types; one frozen source hash.')
