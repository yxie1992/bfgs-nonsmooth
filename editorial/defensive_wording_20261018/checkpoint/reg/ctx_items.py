"""Show, for register items, the HEAD text of their lines and the working-tree text of the mapped lines."""
import sys, json, subprocess
sys.path.insert(0, '/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/editorial/lean_coverage')
import extract_items as ex
import resync_register as rr
ROOT = ex.ROOT
st = json.load(open('/tmp/opencode/m44/reg/anchor_status.json'))
cache = {}
def texts(path):
    if path not in cache:
        old = subprocess.run(['git', 'show', 'HEAD:' + path], cwd=ROOT, capture_output=True, text=True).stdout
        new = (ROOT / path).read_text()
        start, end, touched = rr.line_maps(old, new)
        cache[path] = (old.split('\n'), new.split('\n'), start, end)
    return cache[path]
for i in sys.argv[1:]:
    v = st[i]
    old, new, start, end = texts(v['file'])
    a, b = v['lines']
    s, e = start.get(a), end.get(b)
    print(f"== {i} {v['status']} {v['file']}:{a}-{b} anchor: {v['anchor']}")
    print('   OLD:', ' '.join(old[a-1:b]))
    if s is None or e is None or e < s:
        lo = (s or 1) - 1
        print(f'   NEW (lines deleted; around {lo}):', ' '.join(new[max(lo-1,0):lo+1]))
    else:
        print(f'   NEW {s}-{e}:', ' '.join(new[s-1:e]))
