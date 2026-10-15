"""Scratch: compare files of an exported tree with the blobs of a repo commit (read-only)."""
import sys, hashlib, subprocess
from pathlib import Path
tree, rev = Path(sys.argv[1]), sys.argv[2]
repo = '/Users/yxie/Projects/bfgs-nonsmooth'
listing = subprocess.check_output(['git','ls-tree','-r','-z',rev], cwd=repo).decode().strip('\0').split('\0')
blobs = {}
for row in listing:
    meta, name = row.split('\t',1); blobs[name] = meta.split()[2]
changed, missing = [], []
for name, blob in blobs.items():
    p = tree/name
    if not p.is_file(): missing.append(name); continue
    data = p.read_bytes()
    if hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest() != blob: changed.append(name)
extra = []
import os
for dp, dn, fn in os.walk(tree):
    for f in fn:
        rel = str((Path(dp)/f).relative_to(tree))
        if rel not in blobs: extra.append(rel)
print('CHANGED', len(changed)); [print('  M', c) for c in changed]
print('MISSING', len(missing)); [print('  D', c) for c in missing[:50]]
print('UNTRACKED', len(extra)); [print('  ?', c) for c in sorted(extra)[:80]]
