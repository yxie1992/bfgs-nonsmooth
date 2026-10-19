"""For every register item with an anchor in the edited TeX files: is the anchor found
(whitespace-normalized) in the HEAD text and in the working-tree text?"""
import sys, json, subprocess
sys.path.insert(0, '/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/editorial/lean_coverage')
import extract_items as ex
import resync_register as rr
ROOT = ex.ROOT
files = subprocess.run(['git', 'diff', '--name-only', 'HEAD', '--', 'paper', 'companion'], cwd=ROOT,
                       capture_output=True, text=True).stdout.split()
files = [f for f in files if f.endswith('.tex')]
out = {}
for f in files:
    try:
        reg = ex.register_path(f)
    except Exception:
        continue
    if not reg.exists():
        continue
    data = json.loads(reg.read_text())
    old = subprocess.run(['git', 'show', 'HEAD:' + f], cwd=ROOT, capture_output=True, text=True).stdout
    new = (ROOT / f).read_text()
    for it in data['items']:
        a = it.get('anchor')
        if not a:
            continue
        h = bool(rr.anchor_lines(old, a)); n = bool(rr.anchor_lines(new, a))
        out[it['id']] = {'file': f, 'status': it.get('status'), 'head': h, 'now': n, 'lines': it.get('lines'), 'anchor': a}
json.dump(out, open('/tmp/opencode/m44/reg/anchor_status.json', 'w'), indent=1)
import collections
c = collections.Counter((v['head'], v['now']) for v in out.values())
print(c)
per = collections.Counter(v['file'] for v in out.values() if v['head'] and not v['now'])
for k, v in sorted(per.items()): print(v, k)
print('not found at HEAD:', [k for k, v in out.items() if not v['head']][:40])
