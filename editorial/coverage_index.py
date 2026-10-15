"""The Lean coverage registers as part of the claim/proof index.

`build(root, index)` reads every coverage register (`editorial/lean_coverage/register/`)
and returns the ledger entries and the HTML section that `assemble_claim_ledger.py`
adds to `CLAIM_LEDGER.json` and `companion/PROOF_CORRESPONDENCE.html`: every item of
the article and the companion with its status, its Lean declarations (with the
statement as written in the Lean source, or the exact signature from the sealed
declaration index), its targets, and its reason or note.
"""
from pathlib import Path
import collections, html, json, re, sys

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)')
WHERE = re.compile(r'\swhere\s*$')
LEAN_SOURCES = ['bfgs_lean_article/BfgsArticle/**/*.lean', 'bfgs_lean_stage1/BfgsVerification/**/*.lean']
EXTRA_SOURCES = ['editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean',
                 'editorial/satisfaction_review/branch_formal/ArticleBranchRegularity.lean',
                 'editorial/article_formal/ArticleGeometry.lean',
                 'editorial/article_formal/ConvexBalance.lean',
                 'editorial/narrative_rebuild/negative_scaling.lean',
                 'bfgs_lean_stage1/master_report/audit/sources/OriginalClaimInterpretation.lean']
STATUS = [
    ('LEAN', 'a coverage theorem states the claim; its proof is in the named module'),
    ('DEFINITION', 'the item defines notation or an object; the Lean definitions are named'),
    ('PART_OF', 'the item is part of the statement of the target item'),
    ('PROOF', 'the item is a proof of the target item, whose Lean theorem is proved'),
    ('SAME_AS', 'the item restates or weakens the target items'),
    ('OPEN', 'an open question, stated as a Lean proposition without proof'),
    ('NON_CLAIM', 'not a mathematical claim (the reason is given)'),
]


def declarations(root):
    """Fully qualified name -> (path, line, statement as written), textually."""
    found = {}
    paths = [p for pattern in LEAN_SOURCES for p in sorted(root.glob(pattern))]
    paths += [root / p for p in EXTRA_SOURCES if (root / p).exists()]
    for path in paths:
        lines, stack = path.read_text().splitlines(), []
        for i, raw in enumerate(lines):
            line = raw.strip()
            if m := re.match(r'namespace\s+(\S+)', line):
                stack.append(m.group(1))
            elif m := re.match(r'end(?:\s+(\S+))?\s*$', line):
                if stack and (m.group(1) is None or m.group(1) == stack[-1]
                              or stack[-1].endswith('.' + (m.group(1) or ''))):
                    stack.pop()
            elif m := DECL.match(line):
                kind, name = m.group(1), m.group(2)
                qualified = name.removeprefix('_root_.') if name.startswith('_root_.') or not stack \
                    else '.'.join(stack + [name])
                statement = []
                for j in range(i, min(i + 80, len(lines))):
                    text = lines[j]
                    if kind not in ('theorem', 'lemma'):
                        # A definition's body is part of what it states.
                        if j > i and (not text.strip() or text.startswith(('/-', '@[', 'theorem ', 'lemma ',
                                                                            'def ', 'end ', 'namespace '))):
                            break
                        statement.append(text)
                        continue
                    cut = [k for k in (text.find(':='),) if k >= 0]
                    if w := WHERE.search(text):
                        cut.append(w.start())
                    if cut:
                        statement.append(text[:min(cut)].rstrip())
                        break
                    statement.append(text)
                found.setdefault(qualified, (str(path.relative_to(root)), i + 1, '\n'.join(statement).strip()))
    return found


def build(root, index):
    """Ledger entry and HTML section of the coverage registers."""
    root = Path(root)
    sys.path.insert(0, str(root / 'editorial/lean_coverage'))
    import extract_items as ex
    known = declarations(root)
    records, names, counts = [], {}, {}
    for document, files in (('article', ex.ARTICLE), ('companion', ex.COMPANION)):
        counts[document] = collections.Counter()
        for tex in files:
            register = json.loads(ex.register_path(tex).read_text())
            for item in register['items']:
                record = {'document': document, 'file': tex, 'id': item['id'], 'kind': item['kind'],
                          'lines': item['lines'], 'status': item['status']}
                for key in ('labels', 'title', 'anchor', 'of', 'reason', 'note'):
                    if item.get(key):
                        record[key] = item[key]
                if item.get('lean'):
                    record['lean'] = item['lean']
                    for name in item['lean']:
                        if name in names:
                            continue
                        if name in index and index[name].get('signature'):
                            names[name] = {'source': 'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json',
                                           'signature': str(index[name]['signature'])}
                        elif name in known:
                            path, line, statement = known[name]
                            names[name] = {'source': f'{path}:{line}', 'statement': statement}
                        else:
                            raise AssertionError(('Lean name not found', item['id'], name))
                records.append(record)
                counts[document][item['status']] += 1
    summary = {
        'method': 'editorial/lean_coverage/README.md',
        'registers': 'editorial/lean_coverage/register/',
        'checker': 'editorial/lean_coverage/check_coverage.py',
        'axiom_audit': 'bfgs_lean_article/AXIOM_AUDIT.json',
        'kernel_replay': 'bfgs_lean_article/KERNEL_REPLAY.json',
        'statuses': dict(STATUS),
        'items': {d: sum(c.values()) for d, c in counts.items()},
        'items_by_status': {d: dict(sorted(c.items())) for d, c in counts.items()},
        'declarations': 'Statements are the Lean source text of each declaration (section variables and '
                        'opened namespaces apply), or the exact signature from the sealed declaration index.',
    }
    parts = ['<h2>Lean coverage of every item</h2>',
             '<p>Every item of the article and the companion (theorem-like environments, proofs, displays, '
             'tables, figures, headings, and every prose sentence or group of sentences that asserts '
             'mathematics) is classified in the Lean coverage registers (<code>editorial/lean_coverage/register/'
             '</code>; method in <code>editorial/lean_coverage/README.md</code>). The axiom audit '
             '(<code>bfgs_lean_article/AXIOM_AUDIT.json</code>) checks the axioms of every Lean name below, '
             'and the kernel replay (<code>bfgs_lean_article/KERNEL_REPLAY.json</code>) re-checks every '
             'project module through the Lean kernel.</p><ul>']
    parts += ['<li><b>' + s + '</b>: ' + html.escape(t) + '</li>' for s, t in STATUS]
    parts.append('</ul><p>' + '; '.join(
        html.escape(f'{d}: {sum(c.values())} items (' + ', '.join(f'{s} {n}' for s, n in sorted(c.items())) + ')')
        for d, c in counts.items()) + '. ' + html.escape(summary['declarations']) + '</p>')
    current = None
    for record in records:
        if record['file'] != current:
            current = record['file']
            parts.append('<h3>' + html.escape(record['document'].capitalize() + ': ' + current) + '</h3>')
        a, b = record['lines']
        where = f'{record["file"]}:{a}' + (f'-{b}' if b != a else '')
        head = record['id'] + ' — ' + record['status'] + ' — ' + record['kind'] + (
            ': ' + record['title'] if record.get('title') else '')
        parts.append('<details><summary>' + html.escape(head) + '</summary><p>' + html.escape(where) + '</p>')
        if record.get('anchor'):
            parts.append('<p>Begins: “' + html.escape(record['anchor']) + '”</p>')
        if record.get('of'):
            targets = record['of'] if isinstance(record['of'], list) else [record['of']]
            parts.append('<p>Target: ' + html.escape(', '.join(targets)) + '</p>')
        for key, label in (('reason', 'Reason'), ('note', 'Note')):
            if record.get(key):
                parts.append('<p>' + label + ': ' + html.escape(record[key]) + '</p>')
        for name in record.get('lean', []):
            entry = names[name]
            text = entry.get('statement') or entry.get('signature')
            parts.append('<details><summary><code>' + html.escape(name) + '</code> (' + html.escape(entry['source'])
                         + ')</summary><pre>' + html.escape(text) + '</pre></details>')
        parts.append('</details>')
    return summary, records, dict(sorted(names.items())), parts
