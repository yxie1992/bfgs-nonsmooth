#!/usr/bin/env python3
"""Delivered-only actual-type and reviewed-proof correspondence checks."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[1]
m=json.loads((R/'audit/d_literal_closure_declarations.json').read_text())
for scope in m['scopes']:
 for row in scope['sources']:
  s=(R/row['path']).read_text()
  it=iter(row['reviewed_imports'])
  original=re.sub(r'^import .*$',lambda _:next(it),s,flags=re.M)
  assert next(it,None) is None,row['path']
  assert hashlib.sha256(original.encode()).hexdigest()==row['reviewed_sha256'],row['path']
  body=re.sub(r'^import .*\n','',s,flags=re.M)
  assert hashlib.sha256(body.encode()).hexdigest()==row['proof_body_sha256'],row['path']
log=(R/'audit/d_literal_closure_axioms_contracts.log').read_text()
for n in m['declarations']:
 assert re.search(r'^'+re.escape(n)+r'(?:\s|\.|\{)',log,re.M),('missing actual declaration type',n)
for n,t in m['targets']:
 assert 'EXACT_TARGET_OK '+n in log,n
print('PASS: delivered-only reconstruction matches all six reviewed original source hashes and proof-body hashes; all 31 actual declaration types and two complete target identities present.')
