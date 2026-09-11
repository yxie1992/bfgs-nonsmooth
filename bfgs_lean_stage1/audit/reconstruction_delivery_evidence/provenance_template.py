#!/usr/bin/env python3
"""Validate import-only reconstruction delivery without reading excluded scratch."""
from pathlib import Path,PurePosixPath
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
def read(rel):
    p=PurePosixPath(rel);assert not p.is_absolute() and '..' not in p.parts
    q=ROOT.joinpath(*p.parts);r=q.resolve();assert r.is_relative_to(ROOT.resolve())
    assert r.relative_to(ROOT.resolve()).parts[:2]!=('audit','scratch')
    return q.read_bytes()
def sha(raw):return hashlib.sha256(raw).hexdigest()
m=json.loads(read('audit/reconstruction_completion_declarations.json'))
assert m['base_release']=='19c76918cb790c311157c85777aa24a76f185b05'
assert len(m['scopes'])==3 and len(m['declarations'])==len(set(m['declarations']))==85
assert len(m['targets'])==4 and sum(len(s['sources']) for s in m['scopes'])==8
names=[];sources=set()
for scope in m['scopes']:
    assert set(scope['review_evidence'])==set(scope['review_evidence_hashes'])
    for source in scope['sources']:
        assert source['path'] not in sources;sources.add(source['path'])
        raw=read(source['path']);assert sha(raw)==source['sha256']
        lines=raw.decode().splitlines(keepends=True);seen=set()
        for change in source['import_normalizations']:
            i=change['line']-1;assert i not in seen;seen.add(i)
            assert lines[i]==change['delivered_line']=='import '+change['to']+'\n'
            assert change['reviewed_line']=='import '+change['from']+'\n'
            lines[i]=change['reviewed_line']
        assert sha(''.join(lines).encode())==source['reviewed_original_sha256']
    assert [n for row in scope['sources'] for n in row['declarations']]==scope['declarations']
    names+=scope['declarations']
    for path,h in scope['review_evidence_hashes'].items():assert sha(read(path))==h,path
    for role in ['owner_validation','peer_validation']:
        assert scope[role] in scope['review_evidence_hashes']
        text=read(scope[role]).decode();assert re.search(r'^PASS(?:\s*:|\s+\d{4}-)',text,re.M) and 'FAIL' not in text
assert names==m['declarations']
for path,h in m['main_dependency_hashes'].items():assert sha(read(path))==h,path
print('PASS:8 delivered sources reconstruct reviewed original hashes;85 declarations/4 targets;three frozen owner/peer PASS scopes;all main dependencies match;no scratch input.')
