"""Scratch: list statement / labeled-display changes between two trees (read-only)."""
import sys, re, importlib.util, subprocess, json
from pathlib import Path
head = Path(sys.argv[1])            # tree to compare (current)
spec = importlib.util.spec_from_file_location('rc', head/'editorial/scientific_exposition_20260913/refresh_correspondence.py')
rc = importlib.util.module_from_spec(spec); spec.loader.exec_module(rc)
sys.path.insert(0, str(head/'editorial'))
from active_tex_sources import sources
mode = sys.argv[2]   # 'prior' (13 Sep check baseline 91d30da snapshot) or a git rev of the repo
repo = Path('/Users/yxie/Projects/bfgs-nonsmooth')
def old_text(path):
    if mode == 'prior':
        p = rc.PRIOR / path
        return p.read_text() if p.exists() else None
    try:
        return subprocess.check_output(['git','show',f'{mode}:{path}'], cwd=repo, text=True, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        return None
rc.ROOT = head
out = {'statements_changed':[], 'statements_added':[], 'statements_removed':[], 'displays_changed':[], 'displays_added':[], 'displays_removed':[], 'new_files':[]}
for p in sources(head):
    path = str(p.relative_to(head)); text = p.read_text(); prev = old_text(path)
    if prev is None:
        out['new_files'].append(path); continue
    for regex, kind in [(rc.STATEMENT,'statements'),(rc.MATH,'displays')]:
        try:
            b = rc.blocks(prev, regex); a = rc.blocks(text, regex)
        except AssertionError as e:
            out.setdefault('block_errors',[]).append([path, kind, str(e)[:200]]); continue
        for l in sorted(b.keys()-a.keys()): out[kind+'_removed'].append([path,l])
        for l in sorted(a.keys()-b.keys()): out[kind+'_added'].append([path,l])
        for l in sorted(a.keys()&b.keys()):
            if rc.normalize(b[l][1], path) != rc.normalize(a[l][1], path):
                out[kind+'_changed'].append([path,l])
print(json.dumps(out, indent=1))
