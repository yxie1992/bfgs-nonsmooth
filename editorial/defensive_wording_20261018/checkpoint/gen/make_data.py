import json, re
from pathlib import Path
REPO = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
P = Path('/tmp/opencode/m44/companion')
props = []
for g in 'ABCDEF':
    props += json.loads((P / f'proposals_{g}.json').read_text())['proposals']
assert len(props) == 298
override = {
 'B-04R-10': 'In every three phases the supporting errors repeat',
 'C-05G-08': 'This limiting argument uses the stated finite-extension and accessibility hypotheses. '
             'Proposition~\\ref{G:prop:star} gives an obstruction that needs neither continuity nor '
             'boundedness of the certificate field.',
 'E-14E-25': 'The principal Gram-sum identity and the full-BFGS principal-minor hierarchy are also '
             'proved in arbitrary finite dimension.',
}
drop = {'D-07H-14'}
edits = []
for p in props:
    if p['id'] in drop:
        continue
    new = override.get(p['id'], p['new'])
    m = re.fullmatch(r'companion/chapters/(\d\d)_([A-Z])\.tex', p['file'])
    edits.append({'id': p['id'], 'module': m[2], 'kind': p['kind'], 'old': p['old'], 'new': new,
                  'reason': p['reason']})
lo_reason = ('Prior work is attributed directly. The wording still credits Lewis--Overton only with '
             'their analysis of the scalar model under their own line-search conventions, as the '
             'qualify_LO_scalar_attribution transformation requires.')
edits.append({'id': 'M44-04R-LO', 'module': 'R', 'kind': 'positive',
  'old': 'Lewis--Overton~\\cite[Section~5.1]{LO} analyzes the scalar absolute-value model with its stated '
         'line-search conventions. The Euclidean-norm theorem is a known case recovered here.',
  'new': 'the scalar absolute-value model was analyzed by Lewis--Overton~\\cite[Section~5.1]{LO}. '
         'The Euclidean-norm theorem is recovered here as a special case.',
  'reason': lo_reason})
edits.append({'id': 'M44-07H-LO', 'module': 'H', 'kind': 'positive',
  'old': 'The Euclidean-norm consequence is already Guo--Lewis~\\cite[Corollary~4.2]{GL18}, while '
         'Lewis--Overton~\\cite[Section~5.1]{LO} analyzes the scalar absolute-value model with its stated '
         'line-search conventions.',
  'new': 'The Euclidean-norm consequence is due to Guo--Lewis~\\cite[Corollary~4.2]{GL18}, and the '
         'scalar absolute-value model was analyzed by Lewis--Overton~\\cite[Section~5.1]{LO}.',
  'reason': lo_reason})
# order by chapter and position in the current generated chapter
files = {p.stem.split('_')[1]: p for p in (REPO / 'companion/chapters').glob('*.tex')}
texts = {m: f.read_text() for m, f in files.items()}
num = {m: int(f.stem.split('_')[0]) for m, f in files.items()}
for e in edits:
    t = texts[e['module']]
    assert t.count(e['old']) == 1, e['id']
    e['_pos'] = t.index(e['old'])
edits.sort(key=lambda e: (num[e['module']], e['_pos']))
for e in edits:
    del e['_pos']
from collections import Counter
print(len(edits), Counter(e['module'] for e in edits), Counter(e['kind'] for e in edits))
data = {'item': 'M44 in TODO_MANUSCRIPT_REVIEW.md',
        'scope': 'Wording edits of 18 October 2026 that remove defensive or over-qualifying sentences '
                 'from the generated companion chapters. Each old text occurs exactly once in its '
                 'generated chapter and is replaced after all earlier transformations.',
        'kinds': {'caveat': 'removes a disclaimer that only says what a result does not do',
                  'repeat': 'removes a scope restriction already stated once in Chapter 1',
                  'guard': 'removes a guard word such as "actual" or "genuine"',
                  'positive': 'states a result or attribution directly'},
        'edits': edits}
out = REPO / 'editorial/defensive_wording_20261018/companion_edits.json'
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(data, indent=1, ensure_ascii=False) + '\n')
print(out, out.stat().st_size)
