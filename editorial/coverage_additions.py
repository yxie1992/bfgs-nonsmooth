"""Explicit post-release article additions, backed by current coverage sources.

This is a source-correspondence check, not Lean elaboration or kernel evidence.
The September component reviews and their export sets are never extended here.
Both the ledger and the October revision use this manifest gate; the latter
also requires reviewed CHANGES rows for the new units.
"""
from pathlib import Path
import contextlib
import difflib
import hashlib
import io
import json
import re
import subprocess
import sys

from active_tex_sources import sources
import coverage_index
import lean_source

MANIFEST = 'editorial/main_results_scope_20261016/ADDITIONS.json'
BASE = '61453638c9e86c7fce2cba0078da9fa0fe6f0e16'
REVISION = 'main_results_scope_20261016'
CORRECTION = 'M42'
STATEMENT = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}.*?\\end\{\1\}', re.S)
PROOF = re.compile(r'\\begin\{proof\}.*?\\end\{proof\}', re.S)
LABEL = re.compile(r'\\label\{([^}]+)\}')
FINAL = {'LEAN', 'DEFINITION', 'PART_OF', 'PROOF', 'SAME_AS', 'OPEN', 'NON_CLAIM'}
PASSAGE_CANDIDATES = {
    'm42-geometry-scope': {'file': 'paper/sections/geometry.tex',
                           'start_anchor': r'\paragraph{Checking the hypotheses.}', 'end_anchor': None},
    'm42-local-witnesses': {'file': 'paper/sections/local.tex',
                            'start_anchor': 'The infinite-run quantifier here has actual witnesses', 'end_anchor': None},
    'm42-ch07h-existence': {'file': 'companion/chapters/07_H.tex',
                            'start_anchor': 'Existence of an infinite admissible run is a separate issue.',
                            'end_anchor': 'remains open here.'},
}


class AdditionError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AdditionError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def paper_path(path):
    return (isinstance(path, str) and path.startswith('paper/') and path.endswith('.tex')
            and Path(path).as_posix() == path and '..' not in Path(path).parts)


def tex_code(text):
    return re.sub(r'(?m)(?<!\\)%[^\n]*', lambda m: ' ' * len(m.group()), text)


def require_canonical_tex(text, path, label_templates=()):
    """Guard the literal grammar of the existing frozen input/item scanners."""
    require(not re.search(r'\r(?!\n)', text),
            ('Bare CR line endings are unsupported; use LF or CRLF', path))
    code = tex_code(text)
    require('^^' not in code, ('TeX character translation is unsupported in the literal source inventory', path))
    for match in re.finditer(r'\\(input|include|label|begin|end)(?![A-Za-z])', code):
        arg = re.match(r'\{([^{}\\\s]+)\}', code[match.end():])
        require(arg, ('Unsupported noncanonical TeX command spelling', path, match.group()))
        value = arg.group(1)
        if match[1] == 'label' and path == 'companion/preamble.tex' and value == '#1:chapter':
            line = text[text.rfind('\n', 0, match.start()) + 1:text.find('\n', match.end()) if '\n' in text[match.end():] else len(text)]
            require(line in label_templates, ('Changed historical companion label template', path))
            continue
        pattern = r'[A-Za-z0-9_./-]+' if match[1] in {'input', 'include'} else \
                  r'[A-Za-z0-9:._/-]+' if match[1] == 'label' else r'[A-Za-z][A-Za-z0-9*@_-]*'
        require(re.fullmatch(pattern, value), ('Unsupported literal TeX argument', path, match[1], value))
        if match[1] in {'begin', 'end'}:
            require(value not in {k + '*' for k in ['theorem', 'lemma', 'proposition', 'corollary', 'definition', 'proof']},
                    ('Unsupported starred mathematical environment', path, value))


class Additions:
    def __init__(self, root):
        self.root = Path(root)
        sys.path.insert(0, str(self.root / 'editorial/lean_coverage'))
        import extract_items
        self.ex = extract_items
        self.manifest = json.loads((self.root / MANIFEST).read_text())
        data = self.manifest
        require(set(data) == {'schema_version', 'revision', 'baseline_commit', 'correction_item', 'active_inputs', 'labels', 'passages'}
                and data['schema_version'] == 2 and data['revision'] == REVISION
                and data['baseline_commit'] == BASE and data['correction_item'] == CORRECTION,
                'Invalid M42 additions manifest header: ' + MANIFEST)
        require(all(isinstance(data[k], dict) for k in ['active_inputs', 'labels', 'passages']),
                'M42 active_inputs, labels and passages must be objects')
        for path, digest in data['active_inputs'].items():
            require(paper_path(path) and isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest),
                    ('M42 active_inputs maps canonical paper paths to full source hashes', path))
        for label, path in data['labels'].items():
            require(isinstance(label, str) and label and not re.search(r'[{}\s]', label) and paper_path(path),
                    ('M42 labels maps exact labels to canonical paper paths', label))

        self.base_text = {}

        def visit(path):
            if path in self.base_text:
                return
            require(paper_path(path), ('Invalid baseline input path', path))
            result = subprocess.run(['git', 'show', f'{BASE}:{path}'], cwd=self.root, capture_output=True, text=True)
            require(result.returncode == 0, ('M42 baseline history is required', path, result.stderr.strip()))
            self.base_text[path] = result.stdout
            for name in re.findall(r'\\(?:input|include)\{([^}]+)\}', self.ex.strip_comments(result.stdout)):
                visit('paper/' + name + ('' if Path(name).suffix else '.tex'))

        visit('paper/master.tex')
        preamble = subprocess.run(['git', 'show', f'{BASE}:companion/preamble.tex'], cwd=self.root,
                                  capture_output=True, text=True)
        require(preamble.returncode == 0, 'M42 baseline companion preamble history is required')
        label_templates = [line for line in preamble.stdout.splitlines() if line.startswith(r'\newcommand{\StartModule}')]
        self.source_text = {}
        for document in ['paper', 'companion']:
            for path in sources(self.root, document):
                relative = path.relative_to(self.root).as_posix()
                text = path.read_bytes().decode('utf-8')
                require_canonical_tex(text, relative, label_templates)
                self.source_text[relative] = text
        self.text = {p: t for p, t in self.source_text.items() if p.startswith('paper/')}
        self.new_inputs = sorted(self.text.keys() - self.base_text.keys())
        self.base_labels, base_named = self.inventory(self.base_text)
        labels, named = self.inventory(self.text)
        self.new_labels = {k: v for k, v in labels.items() if k not in self.base_labels}
        self.named = {k: v for k, v in named.items() if k not in base_named}
        self.problems = []

        def check(condition, message):
            if not condition:
                self.problems.append(message)

        check(not self.base_text.keys() - self.text.keys(),
              ('Active article inputs removed', sorted(self.base_text.keys() - self.text.keys())))
        check(set(data['active_inputs']) == set(self.new_inputs),
              ('Unlisted or inactive M42 input', sorted(set(data['active_inputs']) ^ set(self.new_inputs))))
        for path, digest in data['active_inputs'].items():
            check(path in self.text and sha(self.root / path) == digest, ('M42 input source hash differs', path))
        check(data['labels'] == self.new_labels, ('Unlisted, misplaced or inactive M42 label', self.new_labels))
        for label, path in self.base_labels.items():
            check(labels.get(label) == path, ('Old article label removed or moved', label, path))
        for label in base_named:
            check(label in named, ('Old named statement removed', label))
        for label in self.named:
            check(label in data['labels'], ('Unlisted new named statement', label))
        # A new unnumbered display in an old input has no label to put in the
        # manifest. Compare the mechanical display sequence with the M42 base:
        # unmatched current displays get explicit CHANGES units too. A changed
        # old unnumbered display is conservatively a newly checked unit.
        self.changed_displays = {}
        base_proofs, current_proofs = {}, {}
        for path in self.base_text.keys() & self.text.keys():
            before = self.ex.items_of(path, text=self.base_text[path])
            after = self.ex.items_of(path, text=self.text[path])
            base_proofs[path] = sum(i['kind'] == 'proof' for i in before)
            current_proofs[path] = sum(i['kind'] == 'proof' for i in after)
            a, b = [i for i in before if i['kind'] == 'display'], [i for i in after if i['kind'] == 'display']
            for op, i, j, k, l in difflib.SequenceMatcher(a=[u['sha256'] for u in a], b=[u['sha256'] for u in b],
                                                        autojunk=False).get_opcodes():
                if op == 'equal':
                    continue
                check(l - k >= j - i, ('Old display removed; extend the reviewed scope before removing units', path))
                self.changed_displays.setdefault(path, set()).update(u['id'] for u in b[k:l])
        self.units, self.passages = {}, {}
        self.prepare_passages()
        self.files = sorted(set(self.new_inputs) | {u['file'] for u in self.named.values()}
                            | set(self.new_labels.values()) | set(self.changed_displays)
                            | {p['file'] for p in self.passages.values()})
        for path in self.files:
            check(path in self.ex.ARTICLE + self.ex.COMPANION,
                  ('Add the active input to the extractor document inventory before integration', path))

        self.statement_items = {}
        self.proof_items = {}
        self.mechanical = {p: self.ex.items_of(p, text=t) for p, t in self.text.items() if p in self.files}
        for path in self.new_inputs:
            self.units['input:' + path] = {**self.unit(path, 0, len(self.text[path])),
                                           'raw_source_sha256': sha(self.root / path)}
        for label, unit in self.named.items():
            path = unit['file']
            own = [i for i in self.mechanical[path] if i['kind'] == unit['kind'] and i['lines'] == unit['lines']
                   and i['id'].endswith('/' + label)]
            require(len(own) == 1, ('New statement has no unique mechanical item', label))
            self.statement_items[label] = own[0]['id']
            self.units['statement:' + label] = {**unit, 'coverage_item': own[0]['id']}
            if unit['kind'] == 'definition':
                continue
            proof = PROOF.search(self.text[path], unit['end'])
            intervening = STATEMENT.search(self.text[path], unit['end'])
            if not proof or (intervening and intervening.start() < proof.start()):
                self.problems.append(('New result needs its following proof in the same input', label))
                continue
            proof_unit = self.unit(path, proof.start(), proof.end())
            own_proof = [i for i in self.mechanical[path] if i['kind'] == 'proof' and i['lines'] == proof_unit['lines']]
            require(len(own_proof) == 1, ('New result has no unique proof item', label))
            self.proof_items[label] = own_proof[0]['id']
            self.units['proof:' + label] = {**proof_unit, 'coverage_item': own_proof[0]['id']}
        for path in base_proofs:
            paired = sum(self.named[label]['file'] == path for label in self.proof_items)
            check(current_proofs[path] <= base_proofs[path] + paired,
                  ('New proof must follow an explicitly added named result', path))
        for path, items in self.mechanical.items():
            scopes = [u['lines'] for key, u in self.units.items() if u['file'] == path and not key.startswith('passage:')]
            for item in items:
                inside = any(a <= item['lines'][0] and item['lines'][1] <= b for a, b in scopes)
                if item['kind'] == 'proof' and path in self.new_inputs:
                    check(item['id'] in self.proof_items.values(), ('Unassociated proof in new input', item['id']))
                if item['kind'] != 'display' or not (inside or item['id'] in self.changed_displays.get(path, set())):
                    continue
                # All new displays, including unnumbered ones, have a change row.
                first, last = item['lines']
                lines = self.text[path].splitlines(keepends=True)
                start, end = len(''.join(lines[:first - 1])), len(''.join(lines[:last]))
                for key in item['labels'] or [item['id']]:
                    self.units['display:' + key] = {**self.unit(path, start, end), 'coverage_item': item['id']}
        self.coverage = None

    def unit(self, path, start, end):
        text = self.source_text[path]
        return {'file': path, 'start': start, 'end': end, 'text': text[start:end],
                'lines': [text[:start].count('\n') + 1, text[:max(start, end - 1)].count('\n') + 1]}

    def prepare_passages(self):
        """Explicit raw-byte review units in existing indexed document sources."""
        declared = self.manifest['passages']
        specs = {}
        for key, spec in declared.items():
            require(re.fullmatch(r'm42-[a-z0-9]+(?:-[a-z0-9]+)*', key)
                    and isinstance(spec, dict)
                    and set(spec) == {'file', 'start_anchor', 'end_anchor', 'sha256', 'coverage'},
                    ('Invalid M42 passage authorization', key))
            require(isinstance(spec['sha256'], str) and re.fullmatch('[0-9a-f]{64}', spec['sha256'])
                    and isinstance(spec['coverage'], list) and all(isinstance(i, str) and i for i in spec['coverage'])
                    and len(spec['coverage']) == len(set(spec['coverage'])), ('Invalid passage hash or coverage list', key))
            specs[key] = {k: spec[k] for k in ['file', 'start_anchor', 'end_anchor']}
        for key, spec in PASSAGE_CANDIDATES.items():
            if spec['file'] in self.source_text and spec['start_anchor'] in tex_code(self.source_text[spec['file']]):
                require(key not in specs or specs[key] == spec, ('M42 candidate passage boundaries cannot be substituted', key))
                specs[key] = spec
        for key, spec in sorted(specs.items()):
            path = spec['file']
            require(isinstance(path, str) and path in self.ex.ARTICLE + self.ex.COMPANION and path in self.source_text
                    and path not in self.new_inputs, ('Passage needs an existing active indexed document source', key, path))
            base = subprocess.run(['git', 'cat-file', '-e', f'{BASE}:{path}'], cwd=self.root, capture_output=True)
            require(base.returncode == 0, ('Passage file is not an existing M42 baseline source', key, path))
            text, code = self.source_text[path], tex_code(self.source_text[path])
            offsets = []
            for field in ['start_anchor', 'end_anchor']:
                anchor = spec[field]
                if field == 'end_anchor' and anchor is None:
                    offsets.append(len(text))
                    continue
                require(isinstance(anchor, str) and anchor and '\n' not in anchor and '\r' not in anchor,
                        ('Passage boundaries are nonempty single-line anchors (null end means EOF)', key, field))
                require(text.count(anchor) == 1 and code.count(anchor) == 1,
                        ('Passage anchor must occur exactly once in active source text', key, field, anchor))
                offsets.append(text.index(anchor) + (len(anchor) if field == 'end_anchor' else 0))
            start, end = offsets
            require(start < end, ('Passage end precedes its start', key))
            unit = self.unit(path, start, end)
            unit['raw_source_sha256'] = hashlib.sha256(unit['text'].encode('utf-8')).hexdigest()
            current = []
            register = self.ex.register_path(path)
            if register.is_file():
                for item in json.loads(register.read_text())['items']:
                    if item['kind'] != 'prose':
                        continue
                    a, b = item['lines']
                    first, last = unit['lines']
                    if a <= last and first <= b:
                        require(first <= a <= b <= last and item.get('anchor') and
                                self.ex.normalize(item['anchor']) in self.ex.normalize(self.ex.strip_comments(unit['text'])),
                                ('Passage cuts across or misses a registered prose item', key, item['id']))
                        current.append(item['id'])
            proposed = {**spec, 'sha256': unit['raw_source_sha256'], 'coverage': sorted(current)}
            self.passages[key] = proposed
            unit['coverage_items'] = proposed['coverage']
            self.units['passage:' + key] = unit
            if not current:
                self.problems.append(('Passage needs matching current registered prose', key))
            if key not in declared:
                self.problems.append(('Unlisted M42 passage', key))
            elif declared[key] != proposed:
                self.problems.append(('Passage authorization hash/boundaries/prose coverage is stale', key))

    @staticmethod
    def inventory(texts):
        labels, named = {}, {}
        for path, raw in texts.items():
            text = re.sub(r'(?m)(?<!\\)%[^\n]*', lambda m: ' ' * len(m.group()), raw)
            for label in LABEL.findall(text):
                require(label not in labels, ('Duplicate active article label', label, path))
                labels[label] = path
            for match in STATEMENT.finditer(text):
                found = LABEL.findall(match.group())
                require(found, ('Unlabeled named statement', path, match.group()[:100]))
                named[found[0]] = {'file': path, 'kind': match.group(1), 'start': match.start(), 'end': match.end(),
                                   'text': raw[match.start():match.end()],
                                   'lines': [text[:match.start()].count('\n') + 1,
                                             text[:match.end() - 1].count('\n') + 1]}
        return labels, named

    def proposal(self):
        return {'status': 'PROPOSAL', 'verification_performed': False, 'path': MANIFEST, 'problems': self.problems,
                'proposed_manifest': {**self.manifest,
                                      'active_inputs': {p: sha(self.root / p) for p in self.new_inputs},
                                      'labels': self.new_labels, 'passages': self.passages}}

    def validate(self):
        require(not self.problems, ('M42 additions are not authorized/current', self.problems))
        if self.coverage is None:
            self.coverage = Coverage(self)
        return self.coverage


class Coverage:
    """Strict coverage plus source/relationship checks for the addition's files and targets."""
    def __init__(self, additions):
        self.additions, self.root, self.ex = additions, additions.root, additions.ex
        self.items, self.registers, self.register_sources = {}, {}, {}
        for target in sorted((self.root / 'editorial/lean_coverage/register').glob('*.json')):
            register = json.loads(target.read_text())
            path = register['file']
            require(path not in self.registers, ('Duplicate coverage file', path))
            self.registers[path] = register
            self.register_sources[path] = target
            for item in register['items']:
                require(item['id'] not in self.items, ('Duplicate coverage item', item['id']))
                self.items[item['id']] = (path, item)
        self.sealed = json.loads((self.root / 'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json').read_text())
        paths = [p for pattern in coverage_index.LEAN_SOURCES for p in sorted(self.root.glob(pattern))]
        paths += [self.root / p for p in coverage_index.EXTRA_SOURCES if (self.root / p).is_file()]
        self.lexical = lean_source.Sources(self.root, paths) if additions.files else None
        self.current, self.source_names = {}, set()
        self.checked, self.visiting, self.hashes, self.mechanical = set(), set(), {}, {}
        if additions.files:
            for path in additions.files:
                module_path = 'bfgs_lean_article/' + self.ex.lean_module(path).replace('.', '/') + '.lean'
                if module_path in self.lexical.errors:
                    raise self.lexical.errors[module_path]
            import check_coverage
            output = io.StringIO()
            # Keep every existing status/hash/docstring check. Only replace its
            # approximate source-name callback with the lexical source inventory.
            original = check_coverage.lean_declarations
            try:
                check_coverage.lean_declarations = self.lexical.names_in_file
                with contextlib.redirect_stdout(output):
                    code = check_coverage.check(additions.files, strict=True)
            finally:
                check_coverage.lean_declarations = original
            require(code == 0, ('M42 needs complete strict current coverage', output.getvalue()))
        for path in additions.files:
            require(path in self.registers, ('Missing coverage register', path))
            require(self.ex.register_path(path).is_file()
                    and json.loads(self.ex.register_path(path).read_text())['file'] == path,
                    ('Register file identifies another source', path))
            require(self.registers[path].get('lean_module') == self.ex.lean_module(path),
                    ('Addition coverage must use its source file\'s coverage module', path))
            for item in self.registers[path]['items']:
                self.check_item(item['id'])
        for label, item_id in additions.statement_items.items():
            _, item = self.items[item_id]
            kind = additions.named[label]['kind']
            require(item['status'] == ('DEFINITION' if kind == 'definition' else 'LEAN'),
                    ('A new named result needs its own coverage theorem (a definition needs DEFINITION)', label))
            if kind != 'definition':
                primary = self.current[item['lean'][0]]
                require(primary['kind'] in {'theorem', 'lemma'},
                        ('Named result coverage is not a theorem', label, item['lean'][0]))
                proof_id = additions.proof_items[label]
                _, proof = self.items[proof_id]
                require(proof['status'] == 'PROOF' and proof.get('of') in (item_id, [item_id]),
                        ('Proof does not prove its following-source governing statement', label, proof_id))

    def check_item(self, item_id):
        require(item_id not in self.visiting, ('Cyclic coverage relationship', item_id))
        if item_id in self.checked:
            return
        require(item_id in self.items, ('Unknown coverage target', item_id))
        self.visiting.add(item_id)
        path, item = self.items[item_id]
        require(path in self.ex.ARTICLE + self.ex.COMPANION, ('Coverage target is outside indexed sources', item_id))
        require(self.register_sources[path] == self.ex.register_path(path)
                and self.register_sources[path].resolve().is_relative_to(self.root.resolve()),
                ('Coverage target does not use its canonical register', item_id))
        require(self.registers[path].get('lean_module') == self.ex.lean_module(path),
                ('Coverage target must use its source file\'s coverage module', item_id))
        require(path in self.additions.source_text, ('Coverage target is not an active document input', item_id))
        text = (self.root / path).read_text()
        lines = self.ex.strip_comments(text).split('\n')
        span = item.get('lines')
        require(isinstance(span, list) and len(span) == 2 and all(type(n) is int for n in span)
                and 1 <= span[0] <= span[1] <= len(lines), ('Invalid current coverage lines', item_id))
        if item['kind'] == 'prose':
            segment = '\n'.join(lines[span[0] - 1:span[1]])
            require(item.get('anchor') and self.ex.normalize(item['anchor']) in self.ex.normalize(segment),
                    ('Prose anchor is not in its current lines', item_id))
            self.hashes[item_id] = self.ex.digest(segment)
        else:
            if path not in self.mechanical:
                entries = self.ex.items_of(path)
                self.mechanical[path] = {i['id']: i for i in entries}
                require(len(entries) == len(self.mechanical[path]), ('Duplicate mechanical item', path))
            current = self.mechanical[path].get(item_id)
            require(current and all(item.get(k) == current[k] for k in
                                    ('kind', 'lines', 'sha256', 'environment', 'labels', 'container')),
                    ('Coverage item source/hash/placement is stale or missing', item_id))
            self.hashes[item_id] = current['sha256']
        status = item.get('status')
        require(status in FINAL, ('Coverage item has no final status', item_id, status))
        names = item.get('lean', [])
        require(isinstance(names, list) and all(isinstance(n, str) and n for n in names),
                ('Invalid Lean names', item_id))
        module = self.registers[path]['lean_module']
        expected = 'bfgs_lean_article/' + module.replace('.', '/') + '.lean'
        for name in names:
            package = any(p.startswith('bfgs_lean_article/') for p in self.lexical.names.get(name, []))
            if name not in self.sealed or package:
                self.current[name] = self.lexical.get(name, expected if name == (names or [None])[0] and item.get('status') == 'LEAN' else None)
        if status in {'LEAN', 'DEFINITION', 'OPEN'}:
            require(names, ('Coverage item needs Lean names', item_id))
        if status == 'LEAN':
            require(names[0] in self.current and self.current[names[0]]['path'] == expected,
                    ('Foreign first Lean name; expected the registered coverage module', item_id, names[0], expected))
        targets = item.get('of', [])
        targets = targets if isinstance(targets, list) else [targets]
        if status in {'PART_OF', 'PROOF', 'SAME_AS'}:
            require(targets and (status == 'SAME_AS' or len(targets) == 1), ('Missing coverage relationship', item_id))
        if status == 'NON_CLAIM':
            require(item.get('reason'), ('NON_CLAIM needs a reason', item_id))
        for target in targets:
            self.check_item(target)
        self.visiting.remove(item_id)
        self.checked.add(item_id)

    def names(self, item_id):
        _, item = self.items[item_id]
        out = list(item.get('lean', []))
        targets = item.get('of', [])
        for target in targets if isinstance(targets, list) else [targets]:
            out += [n for n in self.names(target) if n not in out]
        return out

    def current_index(self, index):
        # Keep the legacy ledger index intact. In the coverage section, use current
        # package text for addition citations even if an old audit has a signature.
        current = dict(index)
        for item_id in self.checked:
            for name in self.items[item_id][1].get('lean', []):
                if name in self.current and self.current[name]['path'].startswith('bfgs_lean_article/'):
                    current.pop(name, None)
        return current

    def index_inputs(self, index, provenance):
        """Feed complete lexical text to the existing index renderer, without editing it."""
        current, sources = self.current_index(index), dict(provenance)
        for name, entry in self.current.items():
            if name not in current:
                current[name] = {'signature': entry['statement']}
                sources[name] = f"{entry['path']}:{entry['line']}"
                self.source_names.add(name)
        return current, sources

    def mark_source_statements(self, declarations):
        # The renderer treats either field identically; the JSON must distinguish
        # source text from a sealed/elaborated signature (SF6 provenance).
        for name in self.source_names:
            entry = declarations[name]
            entry['statement'] = entry.pop('signature')

    def record(self, item_id):
        path, item = self.items[item_id]
        return {'item': item_id, 'status': item['status'], 'sha256': self.hashes[item_id],
                'register': self.register_sources[path].relative_to(self.root).as_posix(),
                'file': path, 'source_sha256': sha(self.root / path), 'lines': item['lines']}

    def receipt(self):
        records = [self.record(i) for i in sorted(self.checked)]
        lean_sources = {self.current[n]['path'] if n in self.current else 'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json'
                        for i in self.checked for n in self.items[i][1].get('lean', [])}
        return {'manifest': MANIFEST, 'sha256': sha(self.root / MANIFEST), 'baseline_commit': BASE,
                'coverage_verified': records,
                'register_sha256': {p: sha(self.root / p) for p in sorted({r['register'] for r in records})},
                'lean_source_sha256': {p: sha(self.root / p) for p in sorted(lean_sources)},
                'passages': self.additions.passages,
                'scope': 'Current source and coverage relationships only; no Lean elaboration or kernel check.'}

    def ledger_records(self, declarations):
        rows = []
        for label, unit in self.additions.named.items():
            item_id = self.additions.statement_items[label]
            proof_id = self.additions.proof_items.get(label)
            ids = [item_id] + ([proof_id] if proof_id else [])
            names = sorted({n for i in ids for n in self.names(i)})
            contracts = {}
            for name in names:
                require(name in declarations, ('Addition name missing from coverage index', label, name))
                entry = dict(declarations[name])
                source = entry['source'].rsplit(':', 1)[0] if 'statement' in entry else entry['source']
                entry['source_sha256'] = sha(self.root / source)
                contracts[name] = entry
            proof = self.additions.units.get('proof:' + label)
            rows.append({'id': label, 'kind': unit['kind'],
                         'location': {'path': unit['file'], 'line': unit['lines'][0], 'sha256': sha(self.root / unit['file'])},
                         'proof_location': {'path': proof['file'], 'line': proof['lines'][0], 'end_line': proof['lines'][1],
                                            'sha256': sha(self.root / proof['file'])} if proof else
                                           {'kind': 'definition_not_a_proved_claim', 'path': unit['file'], 'line': unit['lines'][0]},
                         'source_spans': [], 'full_formal_exports': names,
                         'coverage_statements': contracts, 'coverage_items': [self.record(i) for i in ids],
                         'status': 'CURRENT_COVERAGE_SOURCE_CORRESPONDENCE',
                         'review': 'Current registered statements and proof relationship; natural-language correspondence '
                                   'needs independent review, and kernel evidence is recorded separately.',
                         'detailed_review': MANIFEST,
                         'coverage_addition': {'revision': REVISION, 'correction_item': CORRECTION,
                                               'manifest_sha256': sha(self.root / MANIFEST),
                                               'receipt': 'editorial/release_20261015/mapping_refresh.json'}})
        return rows
