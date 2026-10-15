#!/usr/bin/env python3
"""Mechanically detectable claim items of the article and the companion.

For every TeX file that the two documents include, this finds
  * theorem-like environments (theorem, lemma, proposition, corollary,
    definition, remark, example, ...), with label and optional title;
  * proofs;
  * displayed formulas (\\[...\\], equation, align, gather, multline, ...),
    with labels and the innermost enclosing statement or proof;
  * figure, table and abstract environments;
  * manual result headings (\\textbf{Theorem 11.1 ...}, \\subsection{Theorem 7.A ...}).
Each item gets an id and a hash of its whitespace-normalized source. Ids of
labelled environments use the label; the others are numbered per kind in
document order. Prose claims cannot be found mechanically; the coverage
register adds them by hand (see README.md).

Usage (any directory):
    python3 editorial/lean_coverage/extract_items.py            # counts per file
    python3 editorial/lean_coverage/extract_items.py --json     # all items
    python3 editorial/lean_coverage/extract_items.py --init     # create or extend register files
"""
from pathlib import Path
import hashlib, json, re, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REGISTER = HERE / 'register'

ARTICLE = ['paper/master.tex'] + [f'paper/sections/{s}.tex' for s in
           ['introduction', 'geometry', 'energy', 'global', 'local', 'failure', 'verification']] + \
          [f'paper/statements/{s}.tex' for s in ['positive_partition', 'negative_upper', 'negative_lower']] + \
          [f'paper/appendices/{s}.tex' for s in ['matrix_algebra', 'planar_geometry', 'seed_certificate', 'lower_curvature']]
COMPANION = ['companion/research_story.tex'] + \
            [f'companion/chapters/{c}.tex' for c in ['01_I', '02_M', '03_T', '04_R', '05_G', '06_F', '07_H', '08_A',
                                                       '09_C', '10_Q', '11_U', '12_D', '13_L', '14_E']] + \
            ['companion/current_verification.tex', 'companion/appendices/seed_certificate.tex',
             'companion/correspondence.tex']

STATEMENTS = {'theorem', 'lemma', 'proposition', 'corollary', 'definition', 'remark', 'example', 'claim',
              'conjecture', 'question', 'problem', 'assumption', 'property', 'note', 'observation'}
CONTAINERS = STATEMENTS | {'proof', 'figure', 'table', 'abstract', 'algorithm'}
DISPLAYS = {'equation', 'equation*', 'align', 'align*', 'gather', 'gather*', 'multline', 'multline*',
            'eqnarray', 'eqnarray*', 'displaymath', 'flalign', 'flalign*', 'alignat', 'alignat*'}
TOKEN = re.compile(r'\\begin\{([^}]+)\}|\\end\{([^}]+)\}|(?<!\\)\\\[|(?<!\\)\\\]')
LABEL = re.compile(r'\\label\{([^}]+)\}')
HEADING = re.compile(r'\\(?:textbf|subsection\*?|subsubsection\*?|paragraph)\{\s*((?:Theorem|Lemma|Proposition|'
                     r'Corollary|Definition|Claim|Conjecture|Question|Open question|Problem)\b[^}]*)\}')


def strip_comments(text):
    """Remove % comments (but not \\%), keeping the line structure."""
    return '\n'.join(re.sub(r'(?<!\\)%.*', '', line) for line in text.split('\n'))


def normalize(text):
    return re.sub(r'\s+', ' ', text).strip()


def digest(text):
    return hashlib.sha256(normalize(text).encode()).hexdigest()[:16]


def register_path(path):
    return REGISTER / f"{'A' if path.startswith('paper/') else 'C'}_{Path(path).stem}.json"


def lean_module(path):
    """Coverage module of a TeX file, e.g. BfgsArticle.Coverage.Article.NegativeLower."""
    stem = Path(path).stem
    name = ''.join(part.capitalize() for part in stem.split('_') if not part.isdigit())
    if stem[:2].isdigit():
        name = f'Ch{stem[:2]}{name}'
    return f"BfgsArticle.Coverage.{'Article' if path.startswith('paper/') else 'Companion'}.{name}"


def items_of(path, text=None):
    """Items of a TeX file (of `text` instead of the working tree's file if given)."""
    text = strip_comments((ROOT / path).read_text() if text is None else text)
    prefix = f"{'A' if path.startswith('paper/') else 'C'}/{Path(path).stem}"
    line = lambda pos: text.count('\n', 0, pos) + 1
    found, stack = [], []
    for match in TOKEN.finditer(text):
        begin, end, token = match.group(1), match.group(2), match.group(0)
        if begin is not None or token == '\\[':
            kind = begin if begin is not None else 'display'
            if kind in CONTAINERS or kind in DISPLAYS or kind == 'display':
                stack.append((kind, match.start(), match.end()))
            continue
        kind = end if end is not None else 'display'
        if not (kind in CONTAINERS or kind in DISPLAYS or kind == 'display'):
            continue
        if not stack or stack[-1][0] != kind:
            raise SystemExit(f'{path}:{line(match.start())}: unbalanced end of {kind}')
        _, start, body_start = stack.pop()
        body = text[body_start:match.start()]
        display = kind in DISPLAYS or kind == 'display'
        # A statement's own label is the first label outside nested displays.
        outside = body if display else re.sub(r'\\begin\{(equation|align|gather|multline)\*?\}.*?\\end\{\1\*?\}|'
                                              r'(?<!\\)\\\[.*?(?<!\\)\\\]', '', body, flags=re.S)
        title = re.match(r'\s*\[([^\]]*)\]', body) if kind in STATEMENTS else None
        found.append({'kind': 'display' if display else kind, 'environment': kind,
                      'lines': [line(start), line(match.end())], 'labels': LABEL.findall(body),
                      'own_label': (LABEL.findall(outside) or [None])[0],
                      'title': normalize(title.group(1)) if title else None,
                      'sha256': digest(text[start:match.end()]), 'start': start, 'end': match.end()})
    if stack:
        raise SystemExit(f'{path}:{line(stack[-1][1])}: unclosed {stack[-1][0]}')
    for match in HEADING.finditer(text):
        found.append({'kind': 'heading', 'environment': None, 'lines': [line(match.start())] * 2, 'labels': [],
                      'own_label': None, 'title': normalize(match.group(1)), 'sha256': digest(match.group(0)),
                      'start': match.start(), 'end': match.end()})
    found.sort(key=lambda r: r['start'])
    counts = {}
    for record in found:
        kind = 'disp' if record['kind'] == 'display' else record['kind']
        if record['own_label'] and record['kind'] != 'display':
            record['id'] = f'{prefix}/{kind}/{record["own_label"]}'
        else:
            counts[kind] = counts.get(kind, 0) + 1
            record['id'] = f'{prefix}/{kind}/{counts[kind]:03d}'
    containers = [r for r in found if r['environment'] in CONTAINERS]
    for record in found:
        enclosing = [r for r in containers if r is not record and r['start'] < record['start'] and record['end'] <= r['end']]
        record['container'] = max(enclosing, key=lambda r: r['start'])['id'] if enclosing else None
    return [{k: r[k] for k in ('id', 'kind', 'environment', 'lines', 'labels', 'title', 'container', 'sha256')}
            for r in found]


def init_registers():
    REGISTER.mkdir(parents=True, exist_ok=True)
    for path in ARTICLE + COMPANION:
        target = register_path(path)
        register = json.loads(target.read_text()) if target.exists() else \
            {'file': path, 'lean_module': lean_module(path), 'items': [], 'discrepancies': []}
        known = {item['id'] for item in register['items']}
        added = 0
        for item in items_of(path):
            if item['id'] not in known:
                register['items'].append(dict(item, status=None))
                added += 1
        target.write_text(json.dumps(register, indent=1, ensure_ascii=False) + '\n')
        print(f'register/{target.name}: {len(register["items"])} items ({added} new)')


def main():
    if '--init' in sys.argv:
        init_registers()
        return
    report = {path: items_of(path) for path in ARTICLE + COMPANION}
    if '--json' in sys.argv:
        print(json.dumps(report, indent=1, ensure_ascii=False))
        return
    for doc, files in (('article', ARTICLE), ('companion', COMPANION)):
        totals = {}
        for path in files:
            counts = {}
            for item in report[path]:
                in_proof = item['kind'] == 'display' and '/proof/' in (item['container'] or '')
                key = 'display in proof' if in_proof else item['kind']
                counts[key] = counts.get(key, 0) + 1
                totals[key] = totals.get(key, 0) + 1
            print(f'{path}: {counts}')
        print(f'== {doc}: {totals}\n')


if __name__ == '__main__':
    main()
