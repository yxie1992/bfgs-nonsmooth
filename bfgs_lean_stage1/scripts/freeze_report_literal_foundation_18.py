#!/usr/bin/env python3
"""Freeze 729 sources after root's optional independently reviewed audit-prefix change."""
from pathlib import Path
import ast,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=next(parent for parent in HERE.parents
          if (parent/'lakefile.toml').is_file() and (parent/'scripts/check.py').is_file())
TAIL='#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity\n'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
record=read(ROOT/'audit/module_m_literal_completion_registration.json')
assert sha((ROOT/'scripts/check.py').read_bytes())==record['check_sha256']
assert sha((ROOT/'BfgsVerification.lean').read_bytes())==record['root_sha256']
audit=(ROOT/'Audit.lean').read_text();assert TAIL in audit
assert sha(audit[audit.index(TAIL):].encode())==record['audit_tail_sha256'],'Existing printed targets/examples changed'
prior=read(ROOT/'audit/report_semialgebraic_path_source_hashes.json')
for path,h in prior.items():
    if path not in ['BfgsVerification.lean','Audit.lean']:assert sha((ROOT/path).read_bytes())==h,path
m=read(ROOT/'audit/module_m_literal_completion_declarations.json')
for scope in m['scopes']:
    for row in scope['sources']:assert sha((ROOT/row['path']).read_bytes())==row['sha256']
files=list((ROOT/'BfgsVerification').glob('*.lean'))+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean']
assert len(files)==729
hashes={str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in sorted(files)}
out=ROOT/'audit/report_literal_foundation_source_hashes.json';assert not out.exists()
out.write_text(json.dumps(hashes,indent=2)+'\n')
print('Frozen729 actual Lean sources;all724 prior library proof files and every old/new Audit tail check preserved.')
print('Enumeration prefix changed after registration:',sha(audit.encode())!=record['registered_audit_sha256'])
print('Full pinned251-target central audit is still required;this freeze does not certify the audit implementation.')
