#!/usr/bin/env python3
"""October 2026 correspondence revision (release tooling T4).

A bounded revision of the three component correspondence reviews
(`editorial/{positive,negative,root}_contract_review.json`), from the 13 September
2026 release commit 3e8b5c6, modelled on
`editorial/scientific_exposition_20260913/refresh_correspondence.py`. That check
rejects every statement change by design; it stays unchanged and is replayed at
its own release commit by `editorial/verify_historical_correspondence.py`.

Every difference from the baseline in a checked unit must be listed, as one row,
in `CHANGES.json` (next to this script):

  statement:<label>      a theorem, lemma, proposition, corollary or definition;
  display:<label>        a labeled equation, align or gather display;
  float:<label>          a table or figure (caption included) whose label a
                         negative or positive review row maps;
  algorithm:line_search  the line-search algorithm block of Section 6;
  proof:<label>          the proof environment governed by a named statement;
  passage:<role>         a proof passage of the negative review that is not a
                         proof environment (explicit start and end anchors);
  root:<id>              the passage at the anchor of a root review record;
  deduction:<n>          the passage at the anchor of the n-th unnumbered
                         deduction of the positive review;
  appendix:<path>        the complete text of the two appendices whose whole text
                         the 13 September revision preserved (lower_curvature.tex,
                         seed_certificate.tex);
  macro:<name>           a macro definition (\\newcommand, \\renewcommand,
                         \\providecommand, \\DeclareMathOperator, \\def) in an active input.

A passage at an anchor runs from the anchor to the end of its paragraph: the
first blank line, the end of the enclosing environment, or the next anchor of
another record in the same file. A `\\label{...}` anchor stands for its
environment; for a labeled display, table or figure with a unit of its own, that
unit. Texts are compared after removing whitespace, except where it separates
TeX tokens (a space that ends a control word before a letter, a control space);
there are no notation aliases. A unit that moved to another file is a change.
Text outside every unit (prose outside root and deduction passages, unmapped
tables and figures and the files they input, headings) is bound only by the
receipt's file hashes: it needs `--write`, but no row.

A row gives the kind, key and file, the change (`changed`, `added`, `removed`,
`moved` with the earlier file in `before_file`, or `anchor` for an anchor
rewritten around unchanged text), the SHA-256 of the normalized text before and
after, the correction items (`M<n>`/`W<n>` of TODO_MANUSCRIPT_REVIEW.md, or
`TODO_LEAN_REVIEW.md: <item title>`; checked for existence only), the Lean
coverage register items with their status and current item hash, the principal
Lean names (found in those items' `lean` fields, directly or through `of`), one
reviewed sentence, and where an anchor changed, the old and the new anchor. A
root row may also replace the record's `scope_review`. Every cited register item
lies in the changed unit; when register items cover the changed lines, at least
one of them is cited; a statement, display, table/figure or proof row cites the
unit's own register item. Macro rows cite no register item.

The revision asserts: the baseline snapshot in `prior_mapping/` matches its
MANIFEST and the blobs of the baseline commit, and the 13 September receipt
names exactly the snapshot's reviews and the two complete appendices;
recomputing the reviews on the baseline snapshot reproduces them (so the
extraction below is the reviewed one); the active TeX inputs are those of the
baseline; statement and display label sets are unchanged except for listed
additions and removals (a named statement may not be added or removed); every
unit equals the baseline, in the same file, except for the listed changes, and
every row matches one current change (hashes included); every anchor resolves
exactly once; the retained evidence subtrees, every unrefreshed field and every
unrefreshed row field are byte-identical to the baseline. It then recomputes
statement bodies, locations, proof passages (start and end lines, passage
hashes) and the article file hashes.

Modes (one is required):
  --snapshot  create prior_mapping/ and its MANIFEST.json from the baseline commit
              (refuses to overwrite an existing snapshot);
  --propose   print, as JSON, every difference that CHANGES.json does not cover,
              as row skeletons, with old and new text, a word diff, candidate
              register items and the TODO text of every cited correction item;
              writes nothing;
  --write     write the three component reviews and the receipt mapping_refresh.json;
  --check     recompute everything in memory and compare bytes; writes nothing.

Needs git history (the baseline commit) and Python 3.11 or newer. It compiles no
Lean and builds no document.
"""
from pathlib import Path
import argparse
import copy
import difflib
import hashlib
import json
import re
import subprocess
import sys

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are required.')

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ED = HERE.relative_to(ROOT).as_posix()
PRIOR = HERE / 'prior_mapping'
CHANGES = HERE / 'CHANGES.json'
RECEIPT = HERE / 'mapping_refresh.json'
BASE = '3e8b5c6ff5f4ef663718c74776ecc78ca3527db4'
REVISION = 'release_20261015'
NAMES = ['positive', 'negative', 'root']
REVIEWS = {name: f'editorial/{name}_contract_review.json' for name in NAMES}
SEPT_RECEIPT = 'editorial/scientific_exposition_20260913/mapping_refresh.json'
COMPANION_INPUTS = ['companion/research_story.tex', 'companion/chapters/13_L.tex']
CHECKERS = ['editorial/verify_release_inputs.py', 'editorial/assemble_claim_ledger.py']
HELPERS = ['editorial/active_tex_sources.py', 'editorial/lean_coverage/extract_items.py']
MANUSCRIPT_TODO = 'TODO_MANUSCRIPT_REVIEW.md'
LEAN_TODO = 'TODO_LEAN_REVIEW.md'
FAILURE = 'paper/sections/failure.tex'
ALGORITHM = ('At a differentiable point $x$, let',
             'No resetting or rescaling of the stored matrix is performed.')
POLYHEDRAL_INPUT = r'\input{statements/positive_partition}'
# The files whose complete text the 13 September revision preserved (its receipt's
# complete_appendix_notation_preservation); each is also one unit here.
COMPLETE_FILES = ['paper/appendices/lower_curvature.tex', 'paper/appendices/seed_certificate.tex']

sys.path.insert(0, str(ROOT / 'editorial'))
sys.path.insert(0, str(ROOT / 'editorial/lean_coverage'))
from active_tex_sources import sources  # noqa: E402
import extract_items  # noqa: E402

STATEMENT = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}.*?\\end\{\1\}', re.S)
MATH = re.compile(r'\\begin\{(equation|align|gather)\}.*?\\end\{\1\}', re.S)
LABEL = re.compile(r'\\label\{([^}]+)\}')
PROOF = re.compile(r'\\begin\{proof\}.*?\\end\{proof\}', re.S)
ENV = re.compile(r'\\(begin|end)\{([^}]+)\}')
BLANK = re.compile(r'\n[ \t]*\n')
SHA = re.compile(r'[0-9a-f]{64}')
# A control word followed by whitespace and a letter, a control word, a control space, a control symbol.
CONTROL = re.compile(r'\\(?:([A-Za-z]+)\s+(?=[A-Za-z])|[A-Za-z]+|\s|.)', re.S)
KINDS = ['statement', 'display', 'float', 'algorithm', 'proof', 'passage', 'root', 'deduction', 'appendix', 'macro']
# Macro definitions in the active inputs: a changed definition changes every statement that uses it.
MACRO = re.compile(r'\\(?:(?:re)?newcommand|providecommand|DeclareMathOperator|def)\*?\s*\{?\s*(\\[A-Za-z@]+)')
FLOATS = {'table', 'table*', 'figure', 'figure*'}
CHANGE_TYPES = {'changed', 'added', 'removed', 'anchor', 'moved'}
ROW_FIELDS = {'id', 'kind', 'key', 'file', 'change', 'before_sha256', 'after_sha256', 'correction_items',
              'coverage', 'principal_lean', 'review', 'anchor', 'end_anchor', 'scope_review', 'before_file'}
FINAL = {'LEAN', 'DEFINITION', 'PART_OF', 'PROOF', 'SAME_AS', 'OPEN', 'NON_CLAIM'}

# Retained evidence of the 13 September revision (its own immutable list).
IMMUTABLE = {
    'positive': ['source_sha256', 'supplemental_formal_evidence', 'formal_project_dependency_closure',
                 'formal_dependency_audit'],
    'negative': ['canonical_contracts', 'canonical_declaration_index', 'canonical_declaration_index_sha256',
                 'claims_sha256', 'source_spans', 'all_span_exports', 'transitive_project_dependencies',
                 'dependency_counts', 'axiom_policy_check', 'supplemental_formal_audit',
                 'supplemental_branch_regularity_audit', 'companion_only_disposition'],
    'root': ['canonical_statement_reviews', 'legacy_formal_dependency_closure', 'legacy_axioms',
             'supplemental_audit', 'supplemental_declarations', 'supplemental_audit_artifacts',
             'mathematical_corrections', 'remaining_math_obligations', 'narrative_supplement_register',
             'supplemental_structural_audit', 'supplemental_branch_regularity_audit',
             'supplemental_cache_binding', 'satisfaction_review'],
}
# The only fields this revision recomputes; everything else stays byte-identical.
REFRESHED = {
    'positive': {'statements', 'equation_mappings', 'unnumbered_mathematical_deductions', 'article_files',
                 'article_sha256'},
    'negative': {'article_labels', 'article_file_sha256'},
    'root': {'records', 'article_file_sha256'},
}
ROW_REFRESHED = {
    ('positive', 'statements'): {'article_location', 'article_statement', 'proof_location'},
    ('positive', 'equation_mappings'): {'article_location'},
    ('positive', 'unnumbered_mathematical_deductions'): {'anchor', 'article_location'},
    ('negative', 'article_labels'): {'article_file', 'line', 'proof_locations'},
    ('root', 'records'): {'anchor', 'article_location', 'scope_review'},
}
PROOF_REFRESHED = {'start_anchor', 'start_line', 'end_line', 'passage_sha256', 'end_anchor_exclusive'}
ANNOTATION = 'october_revision_changes'
PROVENANCE = 'october_correspondence_revision'
HISTORICAL_FIELDS = {
    'negative.display_preservation_check': 'Display preservation record of the narrative rebuild; historical, not re-asserted (October display changes are listed rows).',
    'positive.scientific_exposition_revision': '13 September revision provenance; kept as history.',
    'negative.scientific_exposition_revision': '13 September revision provenance; kept as history.',
    'root.scientific_exposition_revision': '13 September revision provenance; kept as history.',
}


class RevisionError(Exception):
    pass


def require(condition, *message):
    if not condition:
        raise RevisionError(message[0] if len(message) == 1 else message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(Path(path).read_bytes())


def encoded(data):
    return (json.dumps(data, indent=2, ensure_ascii=True) + '\n').encode()


def norm(text):
    """Remove whitespace, except where it separates TeX tokens: one space ends a control word before a
    letter (\\le q is not \\leq), and a control space (backslash and a space or line end) stays one
    (a\\ b is not a\\b). A control symbol such as \\\\ is read first, so \\\\ x and \\\\x agree."""
    def mark(match):
        if match.group(1):
            return '\\' + match.group(1) + '\x00'
        if match.group(0)[1:].isspace():
            return '\\\x00'
        return match.group(0)
    return re.sub(r'\s+', '', CONTROL.sub(mark, text)).replace('\x00', ' ')


def nhash(text):
    return digest(norm(text).encode())


def readable(text):
    return re.sub(r'\s+', ' ', text).strip()


def line(text, offset):
    return text[:offset].count('\n') + 1


def git(*argv, binary=False):
    result = subprocess.run(['git', *argv], cwd=ROOT, capture_output=True)
    require(result.returncode == 0, 'Git history with the baseline commit is required (restore it first): git '
            + ' '.join(argv) + ': ' + result.stderr.decode(errors='replace').strip())
    return result.stdout if binary else result.stdout.decode()


class Tree:
    """Text of the repository files, from the working tree or from the baseline snapshot."""

    def __init__(self, base, name):
        self.base, self.name = base, name
        self.cache = {}

    def read(self, path):
        if path not in self.cache:
            target = self.base / path
            require(target.is_file(), f'Missing file in the {self.name}: {path}')
            self.cache[path] = target.read_text()
        return self.cache[path]

    def exists(self, path):
        return (self.base / path).is_file()


def blocks(text, regex, path):
    out = {}
    for match in regex.finditer(text):
        labels = LABEL.findall(match.group())
        require(labels, ('Unlabeled mathematical block', path, match.group()[:120]))
        for label in labels if regex is MATH else labels[:1]:
            require(label not in out, ('Duplicate block label', path, label))
            out[label] = (match.group(1), match.group(), match.start(), match.end())
    return out


def macro_definitions(text):
    """(name, start, end) of each macro definition: from the command to the end of its line, extended
    while braces opened in the definition are still open."""
    out = []
    for match in MACRO.finditer(text):
        depth, i = 0, match.start()
        while i < len(text):
            c = text[i]
            if c == '\\':
                i += 2
                continue
            depth += (c == '{') - (c == '}')
            if c == '\n' and depth <= 0:
                break
            i += 1
        out.append((match.group(1), match.start(), i))
    return out


def find_unique(text, anchor, where):
    count = text.count(anchor)
    if count != 1:
        return None, count
    return text.index(anchor), 1


def unique(text, anchor, where):
    offset, count = find_unique(text, anchor, where)
    require(offset is not None, ('Anchor must occur exactly once', where, anchor, count))
    return offset


def proof_after(text, start, where):
    match = PROOF.search(text, start)
    require(match, ('No proof after the governing statement', where))
    intervening = STATEMENT.search(text, start)
    require(not intervening or match.start() < intervening.start(),
            ('A different statement intervenes before the proof', where))
    return match


def environment_end(text, start):
    """Offset of the first \\end{...} after start that closes an environment opened before start."""
    depth = 0
    for match in ENV.finditer(text, start):
        if match.group(1) == 'begin':
            depth += 1
        elif depth:
            depth -= 1
        else:
            return match.start()
    return len(text)


def enclosing_environment(text, offset, where, required=True):
    """(start, end) of the innermost environment around offset; None if there is none and not required."""
    stack = []
    for match in ENV.finditer(text):
        if match.start() >= offset:
            break
        if match.group(1) == 'begin':
            stack.append(match)
        else:
            require(stack and stack[-1].group(2) == match.group(2), ('Unbalanced environments before an anchor', where))
            stack.pop()
    if not stack and not required:
        return None
    require(stack, ('Label anchor outside every environment', where))
    opening = stack[-1]
    depth = 0
    for match in ENV.finditer(text, opening.start()):
        if match.group(2) != opening.group(2):
            continue
        depth += 1 if match.group(1) == 'begin' else -1
        if depth == 0:
            return opening.start(), match.end()
    raise RevisionError(('Unclosed environment around an anchor', where))


def load_reviews(base):
    return {name: json.loads((base / REVIEWS[name]).read_text()) for name in NAMES}


def label_places(tree, paths):
    places = {}
    for path in paths:
        text = tree.read(path)
        for match in LABEL.finditer(text):
            require(match.group(1) not in places, ('Duplicate label', match.group(1), path))
            places[match.group(1)] = {'path': path, 'line': line(text, match.start())}
    return places


def unit_specs(reviews):
    """The proof, passage, root and deduction units named by the baseline reviews."""
    pos, neg, root = (reviews[name] for name in NAMES)
    specs = {}

    def add(key, spec):
        if key in specs:
            require(specs[key] == spec, ('One unit key with two different baseline definitions', key))
        specs[key] = spec

    for row in pos['statements']:
        if row['kind'] != 'definition':
            add('proof:' + row['label'], {'type': 'proof_after', 'label': row['label'],
                                          'polyhedral': row['label'] == 'art:polyhedral'})
    for row in neg['article_labels']:
        for proof in row['proof_locations']:
            if proof['role'] == 'explicit_proof_environment':
                resolution = proof['anchor_resolution']
                require(resolution in {'proof following governing statement', 'unique literal proof opening'},
                        ('Unknown proof anchor resolution', row['label'], resolution))
                spec = {'type': 'proof_after', 'label': proof['governing_label'], 'polyhedral': False} \
                    if resolution == 'proof following governing statement' else \
                    {'type': 'proof_literal', 'label': proof['governing_label'], 'file': proof['article_file'],
                     'anchor': proof['start_anchor']}
                add('proof:' + proof['governing_label'], spec)
            else:
                end = proof['end_anchor_exclusive']
                add('passage:' + proof['role'], {'type': 'passage', 'file': proof['article_file'],
                                                  'anchor': proof['start_anchor'],
                                                  'end_anchor': None if end == 'END_OF_FILE' else end})
    for row in neg['article_labels']:
        add('float:' + row['label'], {'type': 'float', 'file': row['article_file'], 'label': row['label']})
    for row in pos['equation_mappings']:
        add('float:' + row['label'], {'type': 'float', 'file': row['article_location']['path'], 'label': row['label']})
    for row in root['records']:
        add('root:' + row['id'], {'type': 'anchored', 'file': row['article_location']['path'],
                                  'anchor': row['anchor']})
    for i, row in enumerate(pos['unnumbered_mathematical_deductions'], 1):
        add(f'deduction:{i}', {'type': 'anchored', 'file': row['article_location']['path'], 'anchor': row['anchor']})
    add('algorithm:line_search', {'type': 'passage', 'file': FAILURE, 'anchor': ALGORITHM[0],
                                  'end_anchor': ALGORITHM[1], 'inclusive': True})
    for path in COMPLETE_FILES:
        add('appendix:' + path, {'type': 'file', 'file': path})
    return specs


def apply_overrides(specs, rows):
    """Current anchors: the baseline anchors, or the new anchors of listed rows."""
    specs = copy.deepcopy(specs)
    for row in rows:
        key = row['kind'] + ':' + row['key']
        for field, target in [('anchor', 'anchor'), ('end_anchor', 'end_anchor')]:
            if field not in row:
                continue
            require(key in specs and target in specs[key], ('Anchor change for a unit without that anchor', row['id'], key))
            require(row[field]['old'] == specs[key][target],
                    ('Listed old anchor differs from the baseline anchor', row['id'], field))
            specs[key][target] = row[field]['new']
    return specs


def compute_units(tree, paths, specs):
    """Every checked unit of a tree. Returns (units, problems, statements)."""
    units, problems, named = {}, [], {}
    for path in paths:
        text = tree.read(path)
        for label, (kind, body, start, end) in blocks(text, STATEMENT, path).items():
            require(label not in named, ('Duplicate statement label', label))
            named[label] = {'path': path, 'kind': kind, 'body': body, 'start': start, 'end': end}
            units['statement:' + label] = {'file': path, 'start': start, 'end': end, 'text': body, 'kind': kind}
        for label, (kind, body, start, end) in blocks(text, MATH, path).items():
            require('display:' + label not in units, ('Duplicate display label', label))
            units['display:' + label] = {'file': path, 'start': start, 'end': end, 'text': body, 'kind': kind}
        for name, start, end in macro_definitions(text):
            key, n = 'macro:' + name, 1
            while key in units:
                n += 1
                key = f'macro:{name}#{n}'
            units[key] = {'file': path, 'start': start, 'end': end, 'text': text[start:end]}
    cutoffs = {}
    for key, spec in specs.items():
        if spec['type'] == 'anchored' and not spec['anchor'].startswith('\\label{'):
            text = tree.read(spec['file'])
            offset, _ = find_unique(text, spec['anchor'], key)
            if offset is not None:
                cutoffs.setdefault(spec['file'], []).append(offset)
    for key, spec in sorted(specs.items()):
        where = (tree.name, key)
        if spec['type'] == 'float':
            # A mapped label in a table or figure: the environment, caption included.
            if 'statement:' + spec['label'] in units or 'display:' + spec['label'] in units:
                continue
            text = tree.read(spec['file'])
            anchor = '\\label{' + spec['label'] + '}'
            offset, count = find_unique(text, anchor, key)
            if offset is None:
                problems.append({'key': key, 'file': spec['file'], 'problem': 'label not unique', 'label': spec['label'],
                                 'occurrences': count})
                continue
            around = enclosing_environment(text, offset, where, required=False)
            if around is None or ENV.match(text, around[0]).group(2) not in FLOATS:
                continue
            begin, end = around
            units[key] = {'file': spec['file'], 'start': begin, 'end': end, 'text': text[begin:end],
                          'environment': ENV.match(text, begin).group(2)}
        elif spec['type'] == 'file':
            text = tree.read(spec['file'])
            units[key] = {'file': spec['file'], 'start': 0, 'end': len(text), 'text': text}
        elif spec['type'] == 'proof_after':
            statement = named.get(spec['label'])
            if statement is None:
                problems.append({'key': key, 'problem': 'governing statement missing', 'label': spec['label']})
                continue
            path = statement['path']
            text = tree.read(path)
            start = statement['end']
            if spec['polyhedral']:
                path = 'paper/sections/local.tex'
                text = tree.read(path)
                start = unique(text, POLYHEDRAL_INPUT, where) + len(POLYHEDRAL_INPUT)
            match = proof_after(text, start, where)
            units[key] = {'file': path, 'start': match.start(), 'end': match.end(), 'text': match.group(),
                          'opening': match.group().splitlines()[0], 'resolution': 'proof following governing statement'}
        elif spec['type'] == 'proof_literal':
            text = tree.read(spec['file'])
            offset, count = find_unique(text, spec['anchor'], key)
            if offset is None:
                problems.append({'key': key, 'file': spec['file'], 'problem': 'anchor not unique',
                                 'anchor': spec['anchor'], 'occurrences': count})
                continue
            match = PROOF.match(text, offset)
            require(match, ('Literal proof anchor does not open a proof', where))
            units[key] = {'file': spec['file'], 'start': match.start(), 'end': match.end(), 'text': match.group(),
                          'opening': match.group().splitlines()[0], 'resolution': 'unique literal proof opening'}
        elif spec['type'] == 'passage':
            text = tree.read(spec['file'])
            start, count = find_unique(text, spec['anchor'], key)
            if start is None:
                problems.append({'key': key, 'file': spec['file'], 'problem': 'anchor not unique',
                                 'anchor': spec['anchor'], 'occurrences': count})
                continue
            if spec['end_anchor'] is None:
                end = len(text)
            else:
                end, count = find_unique(text, spec['end_anchor'], key)
                if end is None:
                    problems.append({'key': key, 'file': spec['file'], 'problem': 'end anchor not unique',
                                     'end_anchor': spec['end_anchor'], 'occurrences': count})
                    continue
                if spec.get('inclusive'):
                    end += len(spec['end_anchor'])
            require(start < end, ('Passage ends before it starts', where))
            units[key] = {'file': spec['file'], 'start': start, 'end': end, 'text': text[start:end],
                          'anchor': spec['anchor'], 'end_anchor': spec['end_anchor']}
        else:
            text = tree.read(spec['file'])
            start, count = find_unique(text, spec['anchor'], key)
            if start is None:
                problems.append({'key': key, 'file': spec['file'], 'problem': 'anchor not unique',
                                 'anchor': spec['anchor'], 'occurrences': count})
                continue
            label = LABEL.fullmatch(spec['anchor'])
            own = label and next((k + label.group(1) for k in ['display:', 'float:'] if k + label.group(1) in units), None)
            if own:
                # The labeled display, table or figure is its own unit; this record only needs its anchor.
                units[key] = {'file': spec['file'], 'start': start, 'end': start + len(spec['anchor']),
                              'text': spec['anchor'], 'anchor': spec['anchor'], 'delegated': own}
                continue
            if label:
                begin, end = enclosing_environment(text, start, where)
            else:
                begin = start
                ends = [len(text), environment_end(text, start)]
                blank = BLANK.search(text, start)
                if blank:
                    ends.append(blank.start())
                ends += [offset for offset in cutoffs.get(spec['file'], []) if offset > start]
                end = min(ends)
            units[key] = {'file': spec['file'], 'start': begin, 'end': end, 'text': text[begin:end],
                          'anchor': spec['anchor']}
    for unit in units.values():
        text = tree.read(unit['file'])
        unit['lines'] = [line(text, unit['start']), line(text, max(unit['start'], unit['end'] - 1))]
    return units, problems, named


def word_diff(old, new):
    a, b = readable(old).split(' '), readable(new).split(' ')
    out = []
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if op == 'equal':
            chunk = a[i1:i2]
            out.append(' '.join(chunk) if len(chunk) <= 12 else ' '.join(chunk[:6] + ['…'] + chunk[-6:]))
        else:
            if i2 > i1:
                out.append('[-' + ' '.join(a[i1:i2]) + '-]')
            if j2 > j1:
                out.append('{+' + ' '.join(b[j1:j2]) + '+}')
    return ' '.join(out)


def changed_lines(old, new):
    """Current line numbers of the lines of a unit that differ from the baseline."""
    a, b = old['text'].split('\n'), new['text'].split('\n')
    first, out = new['lines'][0], set()
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if op != 'equal':
            out.update(range(first + j1, first + j2) if j2 > j1 else [first + max(j1 - 1, 0)])
    return out


def detect(base_units, cur_units, specs, cur_specs, problems):
    """Differences between the baseline units and the current ones (units with unresolved anchors aside)."""
    found = {}
    unresolved = {problem['key'] for problem in problems}
    for key in sorted((base_units.keys() | cur_units.keys()) - unresolved):
        old, new = base_units.get(key), cur_units.get(key)
        kind, name = key.split(':', 1)
        if old and new:
            if old.get('delegated') or new.get('delegated'):
                require(old.get('delegated') == new.get('delegated'), ('Anchor changed between a label and prose', key))
            before, after = nhash(old['text']), nhash(new['text'])
            moved_anchor = key in specs and (specs[key].get('anchor') != cur_specs[key].get('anchor')
                                             or specs[key].get('end_anchor') != cur_specs[key].get('end_anchor'))
            if before != after:
                change = 'changed'
            elif old['file'] != new['file']:
                change = 'moved'
            elif moved_anchor:
                change = 'anchor'
            else:
                continue
        elif old:
            before, after, change = nhash(old['text']), None, 'removed'
        else:
            before, after, change = None, nhash(new['text']), 'added'
        found[key] = {'kind': kind, 'key': name, 'file': (new or old)['file'], 'change': change,
                      'before_sha256': before, 'after_sha256': after}
        if old and new and old['file'] != new['file']:
            found[key]['before_file'] = old['file']
    return found


def correction_text(item):
    """The TODO paragraph of a correction item (for the review of a row; not a check)."""
    if re.fullmatch(r'[MW]\d+', item):
        text, marker = (ROOT / MANUSCRIPT_TODO).read_text(), '**' + item
        starts = [m.start() for m in re.finditer(re.escape(marker) + r'\b', text)]
    else:
        title = item.split(': ', 1)[-1]
        text = (ROOT / LEAN_TODO).read_text()
        flat = re.sub(r'\s+', ' ', text)
        position = flat.find('**' + re.sub(r'\s+', ' ', title).strip())
        if position < 0:
            return None
        text, starts = flat, [position]
    if not starts:
        return None
    pieces = []
    for start in starts:
        end = re.search(r'\n- \[|\n#|\n\n(?=\S)', text[start:])
        pieces.append(readable(text[start:start + (end.start() if end else 1200)])[:1200])
    return ' | '.join(pieces)


def correction_ids():
    manuscript = (ROOT / MANUSCRIPT_TODO).read_text()
    lean = re.sub(r'\s+', ' ', (ROOT / LEAN_TODO).read_text())
    return set(re.findall(r'\*\*([MW]\d+)\b', manuscript)), lean


class Registers:
    def __init__(self):
        self.files = {}
        self.items = {}
        for target in sorted((ROOT / 'editorial/lean_coverage/register').glob('*.json')):
            register = json.loads(target.read_text())
            self.files[register['file']] = register
            for item in register['items']:
                self.items[item['id']] = (register['file'], item)
        self.mechanical = {}

    def current_hash(self, item_id):
        path, item = self.items[item_id]
        if item['kind'] == 'prose':
            lines = extract_items.strip_comments((ROOT / path).read_text()).split('\n')
            first, last = item['lines']
            segment = '\n'.join(lines[first - 1:last])
            require(extract_items.normalize(item['anchor']) in extract_items.normalize(segment),
                    ('Register prose item anchor is not in its lines (resynchronize the register)', item_id))
            return extract_items.digest(segment)
        if path not in self.mechanical:
            self.mechanical[path] = {entry['id']: entry for entry in extract_items.items_of(path)}
        entry = self.mechanical[path].get(item_id)
        require(entry is not None, ('Register item not found in the current TeX', item_id))
        require(entry['sha256'] == item.get('sha256'), ('Register item hash is stale (resynchronize the register)', item_id))
        return entry['sha256']

    def lean_names(self, item_id, seen=None):
        seen = set() if seen is None else seen
        if item_id in seen or item_id not in self.items:
            return set()
        seen.add(item_id)
        _, item = self.items[item_id]
        names = set(item.get('lean') or [])
        targets = item.get('of')
        for target in (targets if isinstance(targets, list) else [targets] if targets else []):
            names |= self.lean_names(target, seen)
        return names

    def ordered_names(self, item_id, seen=None):
        """Lean names of an item, then of the items it refers to, in register order."""
        seen = set() if seen is None else seen
        if item_id in seen or item_id not in self.items:
            return []
        seen.add(item_id)
        _, item = self.items[item_id]
        names = list(item.get('lean') or [])
        targets = item.get('of')
        for target in (targets if isinstance(targets, list) else [targets] if targets else []):
            names += [n for n in self.ordered_names(target, seen) if n not in names]
        return names

    def candidates(self, unit):
        """Register items of the unit's file whose lines overlap the unit."""
        register = self.files.get(unit['file'])
        if not register:
            return []
        first, last = unit['lines']
        out = []
        for item in register['items']:
            a, b = item['lines']
            if a <= last and first <= b:
                out.append(item)
        return out

    def suggest(self, unit, changed):
        """The register items that most likely cover a changed unit."""
        items = self.candidates(unit)
        same = [i for i in items if i['kind'] != 'prose' and i['lines'] == unit['lines']]
        if same:
            return same[:1]
        span = lambda i: (i['lines'][1] - i['lines'][0], i['lines'][0])
        touched = [i for i in items if any(i['lines'][0] <= n <= i['lines'][1] for n in changed)]
        prose = [i for i in touched if i['kind'] == 'prose']
        return prose or sorted(touched, key=span)[:1] or sorted(items, key=span)[:1]


def validate_row_shape(row, ids):
    require(isinstance(row, dict), ('Change row must be an object', row))
    require(set(row) <= ROW_FIELDS, ('Unknown change-row fields', row.get('id'), sorted(set(row) - ROW_FIELDS)))
    for field in ['id', 'kind', 'key', 'file', 'change', 'review']:
        require(isinstance(row.get(field), str) and row[field], ('Change row needs a non-empty string', row.get('id'), field))
    require(re.fullmatch(r'C\d{3,}', row['id']), ('Change row ids look like C001', row['id']))
    require(row['id'] not in ids, ('Duplicate change row id', row['id']))
    require(row['kind'] in KINDS, ('Unknown change kind', row['id'], row['kind']))
    require(row['change'] in CHANGE_TYPES, ('Unknown change type', row['id'], row['change']))
    for field in ['before_sha256', 'after_sha256']:
        value = row.get(field)
        require(value is None or (isinstance(value, str) and SHA.fullmatch(value)), ('Invalid hash', row['id'], field))
    require('\n' not in row['review'] and len(row['review']) >= 20, ('The review is one sentence', row['id']))
    require(isinstance(row.get('correction_items'), list) and row['correction_items']
            and all(isinstance(x, str) and x for x in row['correction_items']), ('Correction items needed', row['id']))
    require(isinstance(row.get('coverage'), list), ('Coverage must be a list', row['id']))
    for entry in row['coverage']:
        require(isinstance(entry, dict) and set(entry) == {'item', 'status', 'sha256'},
                ('Coverage entries are {item, status, sha256}', row['id']))
    require(isinstance(row.get('principal_lean'), list) and all(isinstance(x, str) and x for x in row['principal_lean']),
            ('principal_lean must be a list of names', row['id']))
    for field in ['anchor', 'end_anchor']:
        if field in row:
            require(isinstance(row[field], dict) and set(row[field]) == {'old', 'new'}
                    and all(isinstance(v, str) and v for v in row[field].values()) and row[field]['old'] != row[field]['new'],
                    ('Anchor changes are {old, new}, different and non-empty', row['id'], field))
    if 'scope_review' in row:
        require(row['kind'] == 'root' and isinstance(row['scope_review'], str) and row['scope_review'],
                ('Only a root row may replace a scope_review', row['id']))


def load_changes():
    require(CHANGES.is_file(), 'Missing ' + ED + '/CHANGES.json')
    table = json.loads(CHANGES.read_text())
    require(isinstance(table, dict) and table.get('schema_version') == 1 and table.get('revision') == REVISION
            and table.get('baseline_commit') == BASE and isinstance(table.get('changes'), list),
            'CHANGES.json must be {schema_version: 1, revision, baseline_commit, changes: [...]}')
    ids = set()
    for row in table['changes']:
        validate_row_shape(row, ids)
        ids.add(row['id'])
    keys = [(row['kind'], row['key']) for row in table['changes']]
    require(len(keys) == len(set(keys)), 'Two change rows for one unit')
    return table


def verify_row(row, found, base_units, cur_units, registers, manuscript_ids, lean_todo):
    """Check one listed row against the detected change, the registers and the correction records."""
    key = row['kind'] + ':' + row['key']
    detected = found[key]
    for field in ['file', 'change', 'before_sha256', 'after_sha256', 'before_file']:
        require(row.get(field) == detected.get(field), ('Listed change is stale; review it again', row['id'], key, field,
                                                row.get(field), detected.get(field)))
    if row['kind'] == 'statement' and row['change'] in {'added', 'removed'}:
        raise RevisionError(('A named statement was added or removed; the component reviews need a reviewed row '
                             'for it, which this revision does not create: extend it explicitly', row['id'], key))
    if row['change'] == 'anchor':
        require('anchor' in row or 'end_anchor' in row, ('An anchor change lists its anchor', row['id']))
    for item in row['correction_items']:
        if re.fullmatch(r'[MW]\d+', item):
            require(item in manuscript_ids, ('Unknown correction item of ' + MANUSCRIPT_TODO, row['id'], item))
        else:
            prefix = LEAN_TODO + ': '
            require(item.startswith(prefix) and len(item) > len(prefix) + 10
                    and '**' + re.sub(r'\s+', ' ', item[len(prefix):]).strip() in lean_todo,
                    ('Correction items are M<n>, W<n> or "' + prefix + '<item title>"', row['id'], item))
    coverage = []
    reachable = set()
    for entry in row['coverage']:
        require(entry['item'] in registers.items, ('Unknown coverage register item', row['id'], entry['item']))
        path, item = registers.items[entry['item']]
        require(item.get('status') == entry['status'], ('Coverage status differs from the register', row['id'], entry['item']))
        require(entry['status'] in FINAL, ('Coverage item has no final status', row['id'], entry['item'], entry['status']))
        current = registers.current_hash(entry['item'])
        require(entry['sha256'] == current, ('Coverage item hash differs from the current item', row['id'], entry['item']))
        reachable |= registers.lean_names(entry['item'])
        coverage.append({'item': entry['item'], 'file': path, 'lines': item['lines'], 'status': entry['status'],
                         'sha256': current})
    if row['change'] != 'removed' and row['kind'] != 'macro':
        require(coverage, ('A change row needs at least one coverage register item', row['id']))
        unit = cur_units[key]
        first, last = unit['lines']
        for c in coverage:
            require(c['file'] == unit['file'] and c['lines'][0] <= last and first <= c['lines'][1],
                    ('Cited coverage item lies outside the changed unit', row['id'], c['item'], unit['file'], unit['lines']))
        old = base_units.get(key)
        changed = changed_lines(old, unit) if old and row['change'] == 'changed' else set(range(first, last + 1))
        touched = {i['id'] for i in registers.candidates(unit)
                   if any(i['lines'][0] <= n <= i['lines'][1] for n in changed)}
        require(not touched or any(c['item'] in touched for c in coverage),
                ('No cited coverage item overlaps the changed lines', row['id'], sorted(changed)[:12], sorted(touched)))
        if row['kind'] in {'statement', 'display', 'float', 'proof'}:
            own = [i['id'] for i in registers.candidates(unit) if i['kind'] != 'prose' and i['lines'] == unit['lines']]
            require(not own or any(c['item'] in own for c in coverage),
                    ('The register item of the changed unit is not cited', row['id'], own))
    missing = [name for name in row['principal_lean'] if name not in reachable]
    require(not missing, ('Principal Lean names not in the cited register items', row['id'], missing))
    require(row['principal_lean'] or not reachable, ('Principal Lean names needed', row['id']))
    return coverage


def match_rows(found, table, base_units, cur_units, registers, strict):
    """Pair rows with detected changes. In strict mode every mismatch is an error."""
    manuscript_ids, lean_todo = correction_ids()
    listed, stale, unmatched, verified = {}, [], [], {}
    for row in table['changes']:
        key = row['kind'] + ':' + row['key']
        if key not in found:
            require(not strict, ('Listed change not found in the current tree', row['id'], key))
            unmatched.append(row['id'])
            continue
        try:
            verified[key] = verify_row(row, found, base_units, cur_units, registers, manuscript_ids, lean_todo)
            listed[key] = row
        except RevisionError as error:
            if strict:
                raise
            stale.append({'id': row['id'], 'key': key, 'reason': str(error.args[0])})
    uncovered = [key for key in found if key not in listed and key not in {s['key'] for s in stale}]
    if strict and uncovered:
        raise RevisionError(('Unlisted change', uncovered[0], found[uncovered[0]]))
    return listed, verified, stale, unmatched, uncovered


def verify_snapshot():
    manifest = json.loads((PRIOR / 'MANIFEST.json').read_text())
    require(manifest.get('baseline_commit') == BASE, 'Snapshot MANIFEST names another baseline commit')
    git('cat-file', '-e', BASE + '^{commit}')
    for path, expected in manifest['files'].items():
        require(sha(PRIOR / path) == expected, ('Changed baseline snapshot', path))
        require(git('show', f'{BASE}:{path}', binary=True) == (PRIOR / path).read_bytes(),
                ('Snapshot file differs from the baseline commit', path))
    # Files as git sees them (tracked, or untracked and not ignored): an ignored .DS_Store is not an input.
    prior = PRIOR.relative_to(ROOT).as_posix()
    listed = {name[len(prior) + 1:] for name in
              git('ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', prior).split('\0') if name}
    listed -= {'MANIFEST.json'}
    require(listed == set(manifest['files']), ('Snapshot files and MANIFEST disagree', sorted(listed ^ set(manifest['files']))))
    sept = json.loads((PRIOR / SEPT_RECEIPT).read_text())
    require(sept['status'] == 'PASS' and all(sept['component_output_sha256'][REVIEWS[n]] == manifest['files'][REVIEWS[n]]
                                             for n in NAMES),
            'The 13 September receipt does not name the snapshot reviews as its outputs')
    return manifest


def baseline_paths():
    """Active article inputs of the baseline, by the active_tex_sources rules on the baseline blobs."""
    found, visiting = [], set()

    def visit(path):
        require(path not in visiting, ('Cyclic baseline input', path))
        if path in found:
            return
        visiting.add(path)
        found.append(path)
        text = re.sub(r'(?m)(?<!\\)%.*$', '', git('show', f'{BASE}:{path}'))
        for name in re.findall(r'\\(?:input|include)\{([^}]+)\}', text):
            target = 'paper/' + name + ('' if Path(name).suffix else '.tex')
            visit(target)
        visiting.remove(path)

    visit('paper/master.tex')
    return found


def snapshot():
    require(not PRIOR.exists(), 'prior_mapping/ exists; a baseline snapshot is never rewritten')
    git('cat-file', '-e', BASE + '^{commit}')
    paths = list(REVIEWS.values()) + [SEPT_RECEIPT] + baseline_paths() + COMPANION_INPUTS
    files = {}
    for path in sorted(set(paths)):
        data = git('show', f'{BASE}:{path}', binary=True)
        target = PRIOR / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        files[path] = digest(data)
    manifest = {'baseline_commit': BASE,
                'scope': 'Byte copies of the baseline commit: the three component reviews, the 13 September receipt, '
                         'every active article TeX input and the two companion files of the root review.',
                'files': files}
    (PRIOR / 'MANIFEST.json').write_bytes(encoded(manifest))
    print('Snapshot of', BASE[:7] + ':', len(files), 'files')


def location(tree, path, anchor, where):
    text = tree.read(path)
    return {'path': path, 'line': line(text, unique(text, anchor, where))}


def refresh(old, tree, units, specs, named, places, annotations, scope_reviews):
    """The refreshed reviews for a tree; with no annotations, the baseline reproduces itself."""
    out = copy.deepcopy(old)
    pos, neg, root = (out[name] for name in NAMES)
    for row in pos['statements']:
        block = named[row['label']]
        text = tree.read(block['path'])
        row['article_location'] = {'path': block['path'], 'line': line(text, block['start'])}
        row['article_statement'] = block['body']
        if row['kind'] == 'definition':
            row['proof_location'] = {'kind': 'definition_not_a_proved_claim', **row['article_location']}
        else:
            unit = units['proof:' + row['label']]
            row['proof_location'] = {'path': unit['file'], 'line': unit['lines'][0],
                                     'end_line': line(tree.read(unit['file']), unit['end']),
                                     'scope': row['proof_location']['scope']}
    for row in pos['equation_mappings']:
        require(row['label'] in places, ('Mapped display label missing', row['label']))
        row['article_location'] = places[row['label']]
    for i, row in enumerate(pos['unnumbered_mathematical_deductions'], 1):
        spec = specs[f'deduction:{i}']
        row['anchor'] = spec['anchor']
        row['article_location'] = location(tree, spec['file'], spec['anchor'], f'deduction:{i}')
    pos['article_files'] = sorted(set(pos['article_files'])
                                  | {r['article_location']['path'] for r in pos['statements'] + pos['equation_mappings']
                                     + pos['unnumbered_mathematical_deductions']}
                                  | {r['proof_location']['path'] for r in pos['statements']})
    pos['article_sha256'] = {p: digest(tree.read(p).encode()) for p in pos['article_files']}
    for row in neg['article_labels']:
        require(row['label'] in places, ('Mapped negative label missing', row['label']))
        row['article_file'], row['line'] = places[row['label']]['path'], places[row['label']]['line']
        for proof in row['proof_locations']:
            if proof['role'] == 'explicit_proof_environment':
                unit = units['proof:' + proof['governing_label']]
                require(unit['file'] == proof['article_file'], ('Proof moved to another file', proof['governing_label']))
                proof['start_anchor'] = unit['opening']
                require(proof['anchor_resolution'] == unit['resolution'], ('Proof resolution changed', row['label']))
                text = tree.read(unit['file'])
                proof['start_line'] = line(text, unit['start'])
                proof['end_line'] = line(text, unit['end'])
            else:
                unit = units['passage:' + proof['role']]
                require(unit['file'] == proof['article_file'], ('Passage moved to another file', proof['role']))
                text = tree.read(unit['file'])
                proof['start_anchor'] = unit['anchor']
                proof['end_anchor_exclusive'] = unit['end_anchor'] or 'END_OF_FILE'
                proof['start_line'] = line(text, unit['start'])
                proof['end_line'] = line(text, unit['end']) - 1
            proof['passage_sha256'] = digest(unit['text'].encode())
    for row in root['records']:
        spec = specs['root:' + row['id']]
        row['anchor'] = spec['anchor']
        row['article_location'] = location(tree, spec['file'], spec['anchor'], 'root:' + row['id'])
        if row['id'] in scope_reviews:
            row['scope_review'] = scope_reviews[row['id']]
    for name in ['negative', 'root']:
        out[name]['article_file_sha256'] = {p: digest(tree.read(p).encode()) for p in out[name]['article_file_sha256']}
    if annotations:
        for row in pos['statements']:
            touched = annotations.get('statement:' + row['label'], []) + annotations.get('proof:' + row['label'], [])
            if touched:
                row[ANNOTATION] = touched
        for row in pos['equation_mappings']:
            if annotations.get('display:' + row['label']):
                row[ANNOTATION] = annotations['display:' + row['label']]
        for i, row in enumerate(pos['unnumbered_mathematical_deductions'], 1):
            if annotations.get(f'deduction:{i}'):
                row[ANNOTATION] = annotations[f'deduction:{i}']
        for row in neg['article_labels']:
            touched = (annotations.get('statement:' + row['label'], []) + annotations.get('display:' + row['label'], [])
                       + annotations.get('float:' + row['label'], []))
            for proof in row['proof_locations']:
                key = ('proof:' + proof['governing_label'] if proof['role'] == 'explicit_proof_environment'
                       else 'passage:' + proof['role'])
                touched += [c for c in annotations.get(key, []) if c not in touched]
            if touched:
                row[ANNOTATION] = touched
        for row in root['records']:
            touched = list(annotations.get('root:' + row['id'], []))
            delegated = units['root:' + row['id']].get('delegated')
            if delegated:
                touched += annotations.get(delegated, [])
            if touched:
                row[ANNOTATION] = touched
    return out


def assert_bounded(old, out):
    """Only the refreshed fields changed; returns the receipt's retained-evidence list."""
    retained = []
    for name in NAMES:
        require(list(out[name]) == list(old[name]) + ([PROVENANCE] if PROVENANCE in out[name] else []),
                ('Top-level fields added, removed or reordered', name))
        for key in old[name]:
            if key not in REFRESHED[name]:
                require(out[name][key] == old[name][key], ('Unrefreshed field changed', name, key))
        for key in IMMUTABLE[name]:
            require(out[name][key] == old[name][key], ('Retained evidence changed', name, key))
            retained.append({'register': name, 'field': key, 'unchanged_sha256': digest(encoded(out[name][key]))})
    for (name, field), allowed in ROW_REFRESHED.items():
        before, after = old[name][field], out[name][field]
        require(len(before) == len(after), ('Rows added or removed', name, field))
        for a, b in zip(before, after):
            require(set(b) - set(a) <= {ANNOTATION}, ('Row gained fields', name, field))
            for key in a:
                if key not in allowed:
                    require(a[key] == b[key], ('Unrefreshed row field changed', name, field, key))
            if field == 'article_labels':
                require(len(a['proof_locations']) == len(b['proof_locations']), 'Proof locations added or removed')
                for p, q in zip(a['proof_locations'], b['proof_locations']):
                    require(set(p) == set(q), ('Proof location fields changed', a['label']))
                    for key in p:
                        if key not in PROOF_REFRESHED:
                            require(p[key] == q[key], ('Unrefreshed proof-location field changed', a['label'], key))
    return retained


def assert_exports(reviews):
    """The 13 September component-phase export checks, on the unchanged spans and declarations."""
    pos, neg, root = (reviews[name] for name in NAMES)
    claims = {r['id']: r for r in json.loads((ROOT / 'bfgs_lean_stage1/master_report/CLAIMS.json').read_text())['claims']}
    index = set(json.loads((ROOT / 'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json').read_text()))
    supplements = json.loads((ROOT / 'editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json').read_text())['supplements']
    for supplement in supplements + [root['supplemental_branch_regularity_audit']]:
        index |= {d['name'] for d in json.loads((ROOT / supplement['declarations']).read_text())}

    def exports(spans):
        return {n for s in spans for n in claims[s]['exports']}

    for row in pos['statements'] + pos['equation_mappings']:
        require(exports(row['source_span_ids']) | set(row.get('primary_declarations', [])) <= index,
                ('Component-phase declaration missing', row['label']))
    for row in neg['article_labels']:
        require(exports(row['corrected_spans']) | set(row['canonical_exports']) <= index,
                ('Negative component-phase declaration missing', row['label']))


def build(mode):
    manifest = verify_snapshot()
    old = load_reviews(PRIOR)
    base_tree, cur_tree = Tree(PRIOR, 'baseline snapshot'), Tree(ROOT, 'current tree')
    paths = [p.relative_to(ROOT).as_posix() for p in sources(ROOT)]
    base_paths = baseline_paths()
    require(sorted(paths) == sorted(base_paths), ('Active article inputs differ from the baseline (a new or removed '
                                                  'input needs an extension of this revision)',
                                                  sorted(set(paths) ^ set(base_paths))))
    require(all(base_tree.exists(p) for p in paths + COMPANION_INPUTS), 'Snapshot lacks an active input')
    sept = json.loads((PRIOR / SEPT_RECEIPT).read_text())
    require(sorted(a['path'] for a in sept['complete_appendix_notation_preservation']) == sorted(COMPLETE_FILES),
            'COMPLETE_FILES differs from the 13 September receipt')
    specs = unit_specs(old)
    base_units, base_problems, base_named = compute_units(base_tree, paths, specs)
    require(not base_problems, ('Baseline anchors do not resolve', base_problems))
    base_places = label_places(base_tree, paths)
    # The extraction below must reproduce the reviewed 13 September values exactly.
    reproduced = refresh(old, base_tree, base_units, specs, base_named, base_places, {}, {})
    for name in NAMES:
        require(encoded(reproduced[name]) == encoded(old[name]),
                ('Recomputing the baseline does not reproduce its reviewed correspondence', name))

    table = load_changes()
    cur_specs = apply_overrides(specs, table['changes'])
    cur_units, cur_problems, cur_named = compute_units(cur_tree, paths, cur_specs)
    found = detect(base_units, cur_units, specs, cur_specs, cur_problems)
    registers = Registers()
    if mode == 'propose':
        return propose(found, table, base_units, cur_units, cur_problems, registers)
    require(not cur_problems, ('Current anchors do not resolve; list the new anchors', cur_problems))
    listed, verified, _, _, _ = match_rows(found, table, base_units, cur_units, registers, strict=True)

    statement_labels = {k for k in base_units if k.startswith('statement:')} | {k for k in cur_units if k.startswith('statement:')}
    for key in statement_labels:
        require(key in base_units and key in cur_units, ('Named statement added or removed', key))
    places = label_places(cur_tree, paths)
    annotations = {}
    for key, row in listed.items():
        annotations.setdefault(key, []).append(row['id'])
    scope_reviews = {row['key']: row['scope_review'] for row in listed.values() if 'scope_review' in row}
    out = refresh(old, cur_tree, cur_units, cur_specs, cur_named, places, annotations, scope_reviews)
    revision = {'revision': REVISION, 'baseline_commit': BASE,
                'scope': 'October 2026 Lean-coverage and correction edition: listed statement, display, proof and '
                         'passage changes with their correction items and Lean coverage register items; locations, '
                         'statement bodies, proof passages and article hashes recomputed; retained evidence unchanged.',
                'changes': CHANGES.relative_to(ROOT).as_posix(), 'receipt': RECEIPT.relative_to(ROOT).as_posix(),
                'previous_revision': 'scientific_exposition_revision'}
    for name in NAMES:
        out[name][PROVENANCE] = revision
    retained = assert_bounded(old, out)
    assert_exports(out)

    def preserved(prefix):
        rows = []
        for key in sorted(base_units):
            if key.startswith(prefix) and key in cur_units and key not in found:
                a, b = base_units[key], cur_units[key]
                rows.append({'unit': key, 'path': b['file'], 'lines': b['lines'],
                             'before_sha256': digest(a['text'].encode()), 'after_sha256': digest(b['text'].encode()),
                             'equal_after_whitespace_removal': True})
        return rows

    changes = []
    for row in table['changes']:
        key = row['kind'] + ':' + row['key']
        a, b = base_units.get(key), cur_units.get(key)
        changes.append({**row,
                        'before': None if a is None else {'path': a['file'], 'lines': a['lines'],
                                                          'raw_sha256': digest(a['text'].encode())},
                        'after': None if b is None else {'path': b['file'], 'lines': b['lines'],
                                                         'raw_sha256': digest(b['text'].encode())},
                        'coverage_verified': verified[key]})
    outputs = {REVIEWS[name]: encoded(out[name]) for name in NAMES}
    receipt = {
        'status': 'PASS', 'revision': REVISION, 'baseline_commit': BASE, 'scope': revision['scope'],
        'script_sha256': sha(Path(__file__)),
        'baseline_manifest_sha256': sha(PRIOR / 'MANIFEST.json'),
        'baseline_snapshot': {'files': len(manifest['files']), 'equal_to_baseline_commit_blobs': True,
                              'september_receipt_names_snapshot_reviews': True,
                              'recomputed_baseline_reproduces_reviews': True},
        'changes_table': {'path': CHANGES.relative_to(ROOT).as_posix(), 'sha256': sha(CHANGES), 'rows': len(table['changes'])},
        'active_article_inputs': {p: sha(ROOT / p) for p in paths},
        'companion_inputs': {p: sha(ROOT / p) for p in COMPANION_INPUTS},
        'normalization': 'All whitespace removed; no notation aliases.',
        'statement_preservation': preserved('statement:'),
        'labeled_display_preservation': preserved('display:'),
        'table_and_figure_preservation': preserved('float:'),
        'proof_passage_preservation': preserved('proof:') + preserved('passage:'),
        'algorithm_preservation': preserved('algorithm:'),
        'complete_file_preservation': preserved('appendix:'),
        'macro_definition_preservation': preserved('macro:'),
        'root_and_deduction_passage_preservation': preserved('root:') + preserved('deduction:'),
        'listed_changes': changes,
        'immutable_evidence_subtrees': retained,
        'unrefreshed_fields_byte_identical': {name: sorted(set(old[name]) - REFRESHED[name]) for name in NAMES},
        'historical_fields_not_reasserted': HISTORICAL_FIELDS,
        'component_output_sha256': {path: digest(data) for path, data in outputs.items()},
        'existing_checker_sha256': {p: sha(ROOT / p) for p in CHECKERS},
        'helper_sha256': {p: sha(ROOT / p) for p in HELPERS},
        'execution': 'Component correspondence refresh and read-only source, register and contract checks only; '
                     'no document or Lean build.',
    }
    outputs[RECEIPT.relative_to(ROOT).as_posix()] = encoded(receipt)
    for path, data in outputs.items():
        if mode == 'write':
            (ROOT / path).write_bytes(data)
        else:
            require((ROOT / path).is_file() and (ROOT / path).read_bytes() == data,
                    ('Correspondence revision is stale', path))
    counts = {kind: sum(1 for r in table['changes'] if r['kind'] == kind) for kind in KINDS}
    print('PASS:', len(receipt['statement_preservation']), 'statements and',
          len(receipt['labeled_display_preservation']), 'labeled displays unchanged;',
          len(table['changes']), 'listed changes', json.dumps({k: v for k, v in counts.items() if v}) + ';',
          'retained evidence unchanged;', 'written' if mode == 'write' else 'current bytes match')
    return 0


def propose(found, table, base_units, cur_units, problems, registers):
    listed, verified, stale, unmatched, uncovered = match_rows(found, table, base_units, cur_units, registers, strict=False)
    numbers = [int(row['id'][1:]) for row in table['changes']]
    next_id = max(numbers, default=0) + 1
    rows, hints = [], []
    previous = {row['kind'] + ':' + row['key']: row for row in table['changes']}
    for key in sorted(uncovered + [s['key'] for s in stale], key=lambda k: (KINDS.index(k.split(':')[0]), k)):
        detected = found[key]
        old, new = base_units.get(key), cur_units.get(key)
        stale_row = next((s for s in stale if s['key'] == key), None)
        if stale_row:
            row_id = stale_row['id']
        else:
            row_id = f'C{next_id:03d}'
            next_id += 1
        candidates = registers.candidates(new) if new else []
        changed = changed_lines(old, new) if old and new else set(range(new['lines'][0], new['lines'][1] + 1)) if new else set()
        chosen = registers.suggest(new, changed) if new else []
        coverage, names = [], []
        for item in chosen:
            try:
                coverage.append({'item': item['id'], 'status': item.get('status'), 'sha256': registers.current_hash(item['id'])})
            except RevisionError as error:
                coverage.append({'item': item['id'], 'status': item.get('status'), 'sha256': None, 'problem': str(error.args[0])})
            names += [n for n in registers.ordered_names(item['id']) if n not in names]
        earlier = previous.get(key) if stale_row else None
        row = {'id': row_id, **detected, 'correction_items': list(earlier['correction_items']) if earlier else [],
               'coverage': coverage, 'principal_lean': names, 'review': ''}
        for field in ['anchor', 'end_anchor']:
            if earlier and field in earlier:
                row[field] = earlier[field]
        rows.append(row)
        hints.append({'id': row_id, 'unit': key, 'stale_row': stale_row,
                      'previous_review': earlier['review'] if earlier else None,
                      'before_lines': old['lines'] if old else None, 'after_lines': new['lines'] if new else None,
                      'changed_lines': sorted(changed),
                      'old_text': readable(old['text']) if old else None,
                      'new_text': readable(new['text']) if new else None,
                      'word_diff': word_diff(old['text'], new['text']) if old and new else None,
                      'candidate_register_items': [{'item': c['id'], 'kind': c['kind'], 'lines': c['lines'],
                                                    'status': c.get('status'), 'lean': c.get('lean', [])[:6]}
                                                   for c in candidates]})
    for problem in problems:
        kind, name = problem['key'].split(':', 1)
        rows.append({'id': f'C{next_id:03d}', 'kind': kind, 'key': name, 'file': problem.get('file'),
                     'change': 'changed', 'before_sha256': None, 'after_sha256': None,
                     ('end_anchor' if 'end_anchor' in problem else 'anchor'):
                         {'old': problem.get('end_anchor', problem.get('anchor')), 'new': ''},
                     'correction_items': [], 'coverage': [], 'principal_lean': [], 'review': ''})
        hints.append({'id': f'C{next_id:03d}', 'unit': problem['key'], 'problem': problem,
                      'next_step': 'Give the new anchor (it must occur exactly once), then run --propose again for the hashes.'})
        next_id += 1
    cited = sorted({item for row in table['changes'] + rows for item in row.get('correction_items', [])})
    report = {'baseline_commit': BASE, 'listed_rows_matching': len(listed), 'stale_rows': stale,
              'correction_item_texts': {item: correction_text(item) for item in cited},
              'rows_without_a_current_change': unmatched, 'unresolved_anchors': problems,
              'uncovered': rows, 'hints': hints}
    print(json.dumps(report, indent=1, ensure_ascii=False))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ['snapshot', 'propose', 'write', 'check']:
        mode.add_argument('--' + name, action='store_true')
    args = parser.parse_args()
    try:
        if args.snapshot:
            snapshot()
            return 0
        return build('propose' if args.propose else 'write' if args.write else 'check')
    except RevisionError as error:
        print('FAIL:', json.dumps(error.args[0], ensure_ascii=False), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
