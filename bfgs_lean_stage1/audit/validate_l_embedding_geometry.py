#!/usr/bin/env python3
"""Validate source hashes and compiler evidence; no mathematical computation."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parent.parent
AUDIT=ROOT/'audit'
m=json.loads((AUDIT/'l_embedding_geometry_declarations.json').read_text())
for item in m['sources']:
    data=(ROOT/item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',data.decode()),item['path']
log=(AUDIT/'l_embedding_geometry_axioms.log').read_text()
reports={name:{a.strip() for a in names.split(',') if a.strip()} for name,names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
reports.update({name:set() for name in re.findall(r"'([^']+)' does not depend on any axioms",log)})
assert set(reports)==set(m['all_declarations']),set(reports)^set(m['all_declarations'])
for name,axioms in reports.items():assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
for suffix in ['build','axioms','contracts']:
    content=(AUDIT/f'l_embedding_geometry_{suffix}.log').read_text()
    assert not re.search(r'\berror:',content),suffix
    if suffix=='build':assert 'Build completed successfully.' in content
print(f"PASS: {len(m['declarations'])} explicit and {len(m['generated'])} generated declarations; complete standard transitive axiom reports; {len(m['sources'])} exact main source hashes; pinned main build.")

contracts=(AUDIT/"l_embedding_geometry_contracts.log").read_text()
for th,tg in m["targets"]:
    assert f"EXACT_TARGET_OK BfgsVerification.LEmbedding.{th} BfgsVerification.LEmbedding.{tg}" in contracts
print("PASS: all four strict exact source geometry targets.")
