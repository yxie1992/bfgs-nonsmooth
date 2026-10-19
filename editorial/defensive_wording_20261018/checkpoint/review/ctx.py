import json, sys, glob
REPO='/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth/'
props={}
for f in sorted(glob.glob('/tmp/opencode/m44/companion/proposals_*.json')):
    for p in json.load(open(f))['proposals']:
        props[p['id']]=p
w=int(sys.argv[1]); ids=sys.argv[2:]
for i in ids:
    p=props[i]; t=open(REPO+p['file']).read(); k=t.find(p['old'])
    line=t.count('\n',0,k)+1
    print(f"=== {i} {p['file']}:{line}")
    print(t[max(0,k-w):k]+'<<<'+p['old']+'>>>'+t[k+len(p['old']):k+len(p['old'])+w])
    print('NEW: '+p['new'])
