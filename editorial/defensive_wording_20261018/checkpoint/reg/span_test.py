"""Test a sentence-span heuristic for prose item lines on the HEAD registers and texts."""
import sys, json, re, subprocess, collections
sys.path.insert(0, '/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/editorial/lean_coverage')
import extract_items as ex
ROOT = ex.ROOT
END = re.compile(r'[.?!](?=[\s\\}$)]|$)')

def anchor_spans(text, anchor):
    words = anchor.split()
    if not words:
        return []
    pat = r'\s+'.join(re.escape(w) for w in words)
    return [(m.start(), m.end()) for m in re.finditer(pat, text)]

def heuristic(text, s, e, anchor):
    start_line = text.count('\n', 0, s) + 1
    if anchor.rstrip().endswith(('.', '?', '!')):
        end_off = e - 1
    else:
        m = END.search(text, e)
        end_off = m.start() if m else e - 1
    end_line = text.count('\n', 0, end_off) + 1
    if end_line - start_line > 6:
        end_line = text.count('\n', 0, e - 1) + 1
    return [start_line, end_line]

stats = collections.Counter()
samples = collections.defaultdict(list)
for reg in sorted(ex.REGISTER.glob('[AC]_*.json')):
    data = json.loads(subprocess.run(['git', 'show', 'HEAD:' + str(reg.relative_to(ROOT))], cwd=ROOT,
                                     capture_output=True, text=True).stdout)
    path = data['file']
    text = subprocess.run(['git', 'show', 'HEAD:' + path], cwd=ROOT, capture_output=True, text=True).stdout
    for it in data['items']:
        if it['kind'] != 'prose' or not it.get('anchor'):
            continue
        a, b = it['lines']
        spans = anchor_spans(text, it['anchor'])
        if not spans:
            stats['nowhere'] += 1; continue
        best = min(spans, key=lambda se: abs(text.count('\n', 0, se[0]) + 1 - a))
        h = heuristic(text, *best, it['anchor'])
        if h == [a, b]:
            stats['exact'] += 1
        elif h[0] != a:
            stats['start differs'] += 1; samples['start'].append((it['id'], [a, b], h))
        elif h[1] < b:
            stats['end earlier'] += 1; samples['earlier'].append((it['id'], [a, b], h))
        else:
            stats['end later'] += 1; samples['later'].append((it['id'], [a, b], h))
print(stats)
for k, v in samples.items():
    print(k, len(v), v[:12])
