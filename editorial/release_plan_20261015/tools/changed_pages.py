"""Scratch: pages whose text differs between two PDFs (PyMuPDF; read-only)."""
import sys, pymupdf, difflib
old, new = pymupdf.open(sys.argv[1]), pymupdf.open(sys.argv[2])
o = [p.get_text() for p in old]; n = [p.get_text() for p in new]
print(f'old {len(o)} pages, new {len(n)} pages')
same = sum(1 for i in range(min(len(o), len(n))) if o[i] == n[i])
changed = [i + 1 for i in range(len(n)) if i >= len(o) or o[i] != n[i]]
print('identical at same index:', same, '| changed/new pages:', len(changed))
print(changed)
