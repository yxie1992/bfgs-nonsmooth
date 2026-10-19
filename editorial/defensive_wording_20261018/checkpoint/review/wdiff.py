import json, sys, difflib, re
def words(s): return re.findall(r'\S+|\s+', s)
def wdiff(a, b, ctx=6):
    A, B = words(a), words(b)
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    out = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            seg = A[i1:i2]
            nonws = [k for k, w in enumerate(seg) if not w.isspace()]
            if len(nonws) > 2 * ctx:
                head = ''.join(seg[:nonws[ctx - 1] + 1]) if out else ''
                tail = ''.join(seg[nonws[-ctx]:]) if (i2 < len(A)) else ''
                out.append(head + ' ... ' + tail)
            else:
                out.append(''.join(seg))
        else:
            if i2 > i1: out.append('[-' + ''.join(A[i1:i2]) + '-]')
            if j2 > j1: out.append('{+' + ''.join(B[j1:j2]) + '+}')
    return ''.join(out).replace('\n', '⏎')
for path in sys.argv[1:]:
    d = json.load(open(path))
    for p in d['proposals']:
        regs = '; '.join(f"{r.get('item','?').split('/',2)[-1]}:{r.get('status','?')[:3]}:{r.get('action','?')}" for r in p.get('register', []))
        print(f"## {p['id']} [{p['kind']}] {regs}")
        print('  ' + wdiff(p['old'], p['new']))
