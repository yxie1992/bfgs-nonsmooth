#!/usr/bin/env python3
"""Validate delivered source correspondence and peer records without scratch input."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
m=json.loads((ROOT/'audit/module_m_literal_completion_declarations.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
for scope in m['scopes']:
    for source in scope['sources']:
        raw=(ROOT/source['path']).read_bytes();assert sha(raw)==source['sha256']
        lines=raw.decode().splitlines(keepends=True)
        seen=set()
        for change in source['import_normalizations']:
            i=change['line']-1;assert i not in seen;seen.add(i)
            assert lines[i]==change['delivered_line']=='import '+change['to']+'\n'
            assert change['reviewed_line']=='import '+change['from']+'\n'
            lines[i]=change['reviewed_line']
        assert sha(''.join(lines).encode())==source['reviewed_original_sha256']
    assert set(scope['review_evidence'])==set(scope['review_evidence_hashes'])
    for path,h in scope['review_evidence_hashes'].items():assert sha((ROOT/path).read_bytes())==h
    for role in ['owner_validation','peer_validation']:
        log=(ROOT/scope[role]).read_text()
        assert re.search(r'^PASS\s*:',log,re.M) and 'FAIL' not in log
for path,h in m['main_dependency_hashes'].items():assert sha((ROOT/path).read_bytes())==h
assert len(m['declarations'])==len(set(m['declarations']))==18
assert len(m['targets'])==2 and sum(len(s['sources']) for s in m['scopes'])==3
print('PASS:3 delivered sources reconstruct reviewed originals;all owner/peer evidence and main dependencies match;18 declarations/2 targets;no scratch input used.')
