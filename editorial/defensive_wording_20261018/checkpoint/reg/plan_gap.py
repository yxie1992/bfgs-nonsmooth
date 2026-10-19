"""Items whose anchor is lost (anchor_status.json) versus the register actions of the proposals."""
import json, collections
st = json.load(open('/tmp/opencode/m44/reg/anchor_status.json'))
lost = {k for k, v in st.items() if v['head'] and not v['now']}
acts = {}
for g in 'ABCDEF':
    for p in json.load(open(f'/tmp/opencode/m44/companion/proposals_{g}.json'))['proposals']:
        for r in p.get('register', []):
            acts.setdefault(r['item'], []).append((p['id'], r['action'], r.get('anchor')))
handled = {i for i, a in acts.items() if any(x[1] in ('retire', 'reanchor') for x in a)}
print('lost', len(lost), 'handled by proposals', len(lost & handled))
rest = sorted(lost - handled)
print('lost, not handled by proposals:', len(rest))
for i in rest:
    print(' ', i, st[i]['status'], st[i]['lines'], '|', st[i]['anchor'][:90], '|', acts.get(i))
extra = sorted(i for i in handled - lost if any(x[1] == 'reanchor' for x in acts[i]))
print('reanchored by proposals although the old anchor survives:', len(extra))
for i in extra:
    print(' ', i, acts[i])
multi = {i: a for i, a in acts.items() if len({x[1] for x in a if x[1] != 'keep'}) > 1 or len([x for x in a if x[1] == 'reanchor']) > 1}
print('items with several actions:', len(multi))
for i, a in sorted(multi.items()):
    print(' ', i, a)
