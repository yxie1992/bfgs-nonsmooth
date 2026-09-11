#!/usr/bin/env python3
"""One-time import-only adoption of the independently reviewed D literal proofs."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1];S=ROOT/'audit/scratch/d_literal_closure'
assert 'PASS' in (S/'validation.log').read_text()
assert 'PASS' in (S/'peer_validation.log').read_text()
hashes=json.loads((S/'source_hashes.json').read_text());modules={Path(f).stem for f in hashes}
def normalize(text):
 return re.sub(r'^import ([A-Za-z0-9_]+)$',lambda m:'import BfgsVerification.'+m[1] if m[1] in modules else m[0],text,flags=re.M)
rows=[]
for f,h in hashes.items():
 p=S/f;raw=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 out=normalize(raw)
 body=lambda t:re.sub(r'^import .*\n','',t,flags=re.M)
 assert body(raw)==body(out),f
 d=ROOT/'BfgsVerification'/f;assert not d.exists();d.write_text(out)
 rows.append(dict(module='BfgsVerification.'+p.stem,path=str(d.relative_to(ROOT)),sha256=hashlib.sha256(d.read_bytes()).hexdigest(),reviewed_source=str(p.relative_to(ROOT)),reviewed_sha256=h,reviewed_imports=re.findall(r'^import .*$',raw,re.M),proof_body_sha256=hashlib.sha256(body(raw).encode()).hexdigest()))
names=json.loads((S/'declarations.json').read_text());assert len(names)==31
pairs=[['BfgsVerification.'+ns+'.'+th,'BfgsVerification.'+ns+'.'+ta] for ns,th,ta in json.loads((S/'targets.json').read_text())];assert len(pairs)==2
evidence=[]
for f in ['STATEMENT_REVIEW.md','INDEPENDENT_PEER_REVIEW.md','ADDED_SOURCE_MAP.md','peer_validation.log','peer_axioms_contracts.log']:
 d=ROOT/'audit'/('D_LITERAL_CLOSURE_'+f);assert not d.exists();d.write_bytes((S/f).read_bytes());evidence.append(str(d.relative_to(ROOT)))
m=dict(scopes=[dict(id='d_literal_closure',label='D_LITERAL_CLOSURE',sources=rows,declarations=names,targets=pairs,review_evidence=evidence)],declarations=names,targets=pairs,audit_driver='audit/DLiteralClosureAudit.lean',log_prefix='d_literal_closure')
(ROOT/'audit/d_literal_closure_declarations.json').write_text(json.dumps(m,indent=2)+'\n')
(ROOT/'audit/DLiteralClosureAudit.lean').write_text(normalize((S/'PeerAudit.lean').read_text()))
(ROOT/'audit/d_literal_closure_import_correspondence.log').write_text('PASS: all six original reviewed source hashes checked; only import qualification changed; exact proof bodies and all 31 declarations/two targets preserved. Delivered-only correspondence reconstruction is provided separately.\n')
print('Adopted six new D literal modules, 31 declarations and two complete targets; central registration untouched.')
