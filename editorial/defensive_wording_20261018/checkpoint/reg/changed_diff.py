import sys, subprocess, difflib, re
sys.path.insert(0, '/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/editorial/lean_coverage')
import extract_items as ex
ROOT = ex.ROOT
ids = sys.argv[1:]
byfile = {}
for i in ids:
    doc, stem = i.split('/')[:2]
    byfile.setdefault((doc, stem), []).append(i)
for (doc, stem), its in byfile.items():
    path = [p for p in subprocess.run(['git', 'diff', '--name-only', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.split() if p.endswith('/' + stem + '.tex')]
    path = [p for p in path if ('companion' in p) == (its[0].startswith('C/'))][0]
    old = subprocess.run(['git', 'show', 'HEAD:' + path], cwd=ROOT, capture_output=True, text=True).stdout
    new = (ROOT / path).read_text()
    oi = {x['id']: x for x in ex.items_of(path, old)}
    ni = {x['id']: x for x in ex.items_of(path, new)}
    for i in its:
        a = old.split('\n')[oi[i]['lines'][0]-1:oi[i]['lines'][1]]
        b = new.split('\n')[ni[i]['lines'][0]-1:ni[i]['lines'][1]]
        aw, bw = ' '.join(a).split(), ' '.join(b).split()
        print('==', i, path)
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, aw, bw, autojunk=False).get_opcodes():
            if tag != 'equal':
                print('  ', tag, '|', ' '.join(aw[max(i1-4,0):i1]), '[-', ' '.join(aw[i1:i2]), '-] {+', ' '.join(bw[j1:j2]), '+}', ' '.join(aw[i2:i2+3]))
