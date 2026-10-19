"""Print the register entries (all fields except sha) of the given item ids."""
import sys, json, glob
REG = '/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/editorial/lean_coverage/register/'
idx = {}
for p in glob.glob(REG + '*.json'):
    for it in json.load(open(p))['items']:
        idx[it['id']] = it
for i in sys.argv[1:]:
    it = idx.get(i)
    if it is None:
        print('==', i, 'NOT FOUND'); continue
    print('==', i, it.get('status'), it.get('lines'))
    for k, v in it.items():
        if k in ('id', 'status', 'lines', 'sha256', 'anchor', 'kind', 'file'):
            continue
        print(f'   {k}: {v}')
