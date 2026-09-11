#!/usr/bin/env python3
"""Check import-only provenance using delivered files only; no scratch reads."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
m=json.loads((ROOT/'audit/semialgebraic_path_completion_declarations.json').read_text())
def sha(data):return hashlib.sha256(data).hexdigest()
for scope in m['scopes']:
 for source in scope['sources']:
  raw=(ROOT/source['path']).read_bytes()
  assert sha(raw)==source['sha256'],source['path']
  lines=raw.decode().splitlines(keepends=True)
  for change in source['import_normalizations']:
   assert lines[change['line']-1]==change['delivered_line']
   assert change['reviewed_line'].startswith('import '+change['from'])
   assert change['delivered_line']==change['reviewed_line'].replace(
    'import '+change['from'],'import '+change['to'],1)
   lines[change['line']-1]=change['reviewed_line']
  assert sha(''.join(lines).encode())==source['reviewed_original_sha256'],source['path']
 for path,expected in scope['review_evidence_hashes'].items():
  assert sha((ROOT/path).read_bytes())==expected,path
 for role in ['owner_validation','peer_validation']:
  log=(ROOT/scope[role]).read_text()
  assert re.search(r'^PASS\s*:',log,re.M) and 'FAIL' not in log,role
for path,expected in m['main_dependency_hashes'].items():
 assert sha((ROOT/path).read_bytes())==expected,path
assert len(m['declarations'])==len(set(m['declarations']))==152
assert len(m['targets'])==16
assert sum(len(s['sources']) for s in m['scopes'])==33
print('PASS:33 delivered sources reverse exactly to reviewed originals;all owner/peer evidence hashes and main dependencies match;152 declarations and16 targets. No scratch input used.')
