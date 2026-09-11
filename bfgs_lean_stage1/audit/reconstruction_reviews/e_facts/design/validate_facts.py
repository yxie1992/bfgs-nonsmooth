import json,hashlib,re
from pathlib import Path
b=Path(__file__).resolve().parents[1]
m=json.loads((b/'declarations.json').read_text())
for s in m['sources']:
 p=b/'lean'/s['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==s['sha256'],p
log=(b/'design/facts_axioms_contracts.log').read_text()
rows=[json.loads(x) for x in re.findall(r'E_FACT_AUDIT (\{[^\n]+\})',log)]
assert {r['declaration'] for r in rows}==set(m['declarations'])
assert len(rows)==len(m['declarations'])==7
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
assert 'E_FACT_TARGET_PASS 2' in log
assert not re.search(r'(^|\n).*error:',log)
print('PASS: one frozen source, seven actual type/standard-axiom reports, two strict checks of one target')
