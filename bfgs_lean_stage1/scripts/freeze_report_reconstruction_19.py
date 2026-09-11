#!/usr/bin/env python3
"""Freeze all737 sources only after preserving the registered cached Audit exactly."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file() and (p/'scripts/check.py').is_file())
TAIL='#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity\n'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(rel):return json.loads((ROOT/rel).read_text())
r=read('audit/reconstruction_completion_registration.json')
for f,key in [('scripts/check.py','check_sha256'),('BfgsVerification.lean','root_sha256'),('Audit.lean','registered_audit_sha256')]:
    assert sha((ROOT/f).read_bytes())==r[key],f
text=(ROOT/'Audit.lean').read_text();assert text.count(TAIL)==1
assert sha(text[:text.index(TAIL)].encode())==r['cached_prefix_sha256']
assert sha(text[text.index(TAIL):].encode())==r['audit_tail_sha256']
prior=read('audit/report_literal_foundation_source_hashes.json');assert len(prior)==729
for f,h in prior.items():
    if f not in ['Audit.lean','BfgsVerification.lean']:assert sha((ROOT/f).read_bytes())==h,f
m=read('audit/reconstruction_completion_declarations.json')
for scope in m['scopes']:
    for row in scope['sources']:assert sha((ROOT/row['path']).read_bytes())==row['sha256'],row['path']
files=sorted((ROOT/'BfgsVerification').glob('*.lean'))+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean'];assert len(files)==737
out=ROOT/'audit/report_reconstruction_source_hashes.json';assert not out.exists()
out.write_text(json.dumps({str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in files},indent=2)+'\n')
print('Frozen737 actual Lean sources;all727 prior library proofs and the complete cached Audit prefix/old checks preserved. Full255-target gate remains required;no whole-report status promotion.')
