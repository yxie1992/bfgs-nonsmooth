"""Scratch: do the anchors of the component reviews still resolve uniquely in a tree? (read-only)"""
import json, sys, hashlib
from pathlib import Path
tree = Path(sys.argv[1])
def rd(p): return json.loads((tree/p).read_text())
root = rd('editorial/root_contract_review.json'); pos = rd('editorial/positive_contract_review.json'); neg = rd('editorial/negative_contract_review.json')
bad = []; moved = 0; total = 0
def check(path, anchor, line, rid):
    global moved, total
    total += 1
    text = (tree/path).read_text(); n = text.count(anchor)
    if n != 1: bad.append((rid, path, n, anchor[:70])); return
    l = text[:text.index(anchor)].count('\n') + 1
    if l != line: moved += 1
for r in root['records']:
    check(r['article_location']['path'], r['anchor'], r['article_location']['line'], r['id'])
for r in pos['unnumbered_mathematical_deductions']:
    check(r['article_location']['path'], r['anchor'], r['article_location']['line'], 'pos.deduction')
for r in neg['article_labels']:
    for p in r['proof_locations']:
        if p['role'] != 'explicit_proof_environment':
            check(p['article_file'], p['start_anchor'], p['start_line'], r['label']+':'+p['role'])
print('anchors checked', total, 'moved', moved, 'broken', len(bad))
for b in bad: print('  BROKEN', b)
changed = {}
for name, d, key in [('positive', pos, 'article_sha256'), ('negative', neg, 'article_file_sha256'), ('root', root, 'article_file_sha256')]:
    changed[name] = [p for p, h in d[key].items() if hashlib.sha256((tree/p).read_bytes()).hexdigest() != h]
print(json.dumps(changed, indent=1))
