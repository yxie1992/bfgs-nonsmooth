#!/usr/bin/env python3
"""Check delivered scoped compilation evidence, without mathematical evaluation."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parent.parent
AUDIT=ROOT/'audit'
m=json.loads((AUDIT/'l_block_splitting_declarations.json').read_text())
for item in m['sources']:
    p=ROOT/item['path'];s=p.read_text()
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],str(p)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',s),str(p)
log=(AUDIT/'l_block_splitting_axioms.log').read_text()
reports={name:{a.strip() for a in names.split(',') if a.strip()} for name,names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
reports.update({name:set() for name in re.findall(r"'([^']+)' does not depend on any axioms",log)})
assert set(reports)==set(m['declarations'])
for name,axioms in reports.items():assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
for suffix in ['build','axioms']:
    s=(AUDIT/f'l_block_splitting_{suffix}.log').read_text()
    assert not re.search(r'\berror:',s),suffix
    if suffix=='build':assert 'Build completed successfully.' in s
print(f"PASS: {len(m['declarations'])} complete main declaration/standard transitive axiom reports, {len(m['sources'])} exact source hashes, pinned main build; no scratch dependency.")
