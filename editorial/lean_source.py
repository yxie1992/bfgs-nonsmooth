"""Conservative lexical Lean declaration lookup for current coverage evidence.

This does not elaborate Lean. It accepts literal, line-leading public commands,
separate namespace/section scopes, ordinary/raw strings, and balanced headers.
Quoted/generated names, command quotations/macros, mutual blocks and ambiguous
headers fail closed when their source is needed. Sealed index evidence is separate.
"""
from pathlib import Path
import re


class SourceError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise SourceError(message)


def code_mask(text, *, preserve_literals=False):
    """Mask comments and, by default, literals, preserving every offset/newline."""
    require('\ufeff' not in text, 'Lean BOM characters are unsupported in current-source lookup')
    out = list(text)
    i, size = 0, len(text)

    def hide(a, b):
        out[a:b] = ['\n' if c == '\n' else ' ' for c in text[a:b]]

    while i < size:
        start = i
        literal = False
        if text.startswith('/-', i):
            i, depth = i + 2, 1
            while i < size and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, 'Unclosed Lean block comment')
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = size if end < 0 else end
        elif text[i] == 'r' and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) \
                and (raw := re.match(r'r(#+)?"', text[i:])):
            literal = True
            stop = '"' + (raw.group(1) or '')
            end = text.find(stop, i + raw.end())
            require(end >= 0, 'Unclosed Lean raw string')
            i = end + len(stop)
        elif text[i] == '"':
            literal = True
            require(i == 0 or text[i - 1] != '!', 'Interpolated Lean strings are unsupported in current-source lookup')
            i += 1
            while i < size:
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise SourceError('Unclosed Lean string')
            require(i <= size, 'Unclosed Lean string escape')
        elif text[i] == '«':
            raise SourceError('Quoted Lean identifiers are unsupported in current-source lookup')
        elif text[i] == '`':
            raise SourceError('Lean quotations are unsupported in current-source lookup')
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) \
                and (char := re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:])):
            literal = True
            i += char.end()
        else:
            i += 1
            continue
        if not literal or not preserve_literals:
            hide(start, i)
    return ''.join(out)


IDENT = r"[^\W\d][\w'₀-₉]*(?:\.[^\W\d][\w'₀-₉]*)*"
NAME = re.compile(IDENT + r'\Z', re.UNICODE)
DECL = re.compile(r'(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)'
                  r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+'
                  r'(?P<name>' + IDENT + r')(?=\s|[:({\[]|$)')
SCOPE = re.compile(r'(namespace|(?:noncomputable\s+)?section|end)(?:\s+(' + IDENT + r'))?\s*\Z')
COMMAND = re.compile(r'(?:import|open|variable|variables|universe|universes|include|omit|attribute|set_option|'
                     r'local|scoped|notation|infix[lr]?|prefix|postfix|example|noncomputable)\b|#')
UNSUPPORTED = re.compile(r'(?:mutual|macro|macro_rules|elab|elab_rules|syntax|initialize|builtin_initialize|export)\b')
TOKEN = re.compile(r':=|[:()\[\]{}⦃⦄⟨⟩]|[^\W\d][\w\']*', re.UNICODE)
CLOSE = {')': '(', ']': '[', '}': '{', '⦄': '⦃', '⟩': '⟨'}


def header_end(code, start, end, name):
    """Body separator outside binders; a type-level `let x := ...` is not it."""
    stack, lets, colon = [], 0, False
    for match in TOKEN.finditer(code, start, end):
        token = match.group()
        if token in CLOSE.values():
            stack.append(token)
        elif token in CLOSE:
            require(stack and stack.pop() == CLOSE[token], ('Unbalanced Lean header delimiters', name))
        elif not stack:
            if token == ':':
                colon = True
            elif token == 'let':
                lets += 1
            elif token in {'letI', 'letI\'', 'have', 'do', 'by', 'rec'}:
                raise SourceError(('Unsupported term in Lean declaration header', name, token))
            elif token == ':=':
                if lets:
                    lets -= 1
                else:
                    require(colon, ('Lean result needs an explicit complete type', name))
                    return match.start()
            elif token == 'where':
                require(colon and not lets, ('Incomplete type or unfinished let in Lean declaration header', name))
                return match.start()
    raise SourceError(('No complete supported Lean declaration header', name))


class Module:
    def __init__(self, path, text):
        self.path, self.text = path, text
        self.code = code_mask(text)
        self.entries, scopes, namespace, commands = {}, [], [], []
        offset, attributes = 0, None
        for number, line in enumerate(self.code.splitlines(keepends=True), 1):
            raw = text[offset:offset + len(line)]
            stripped = line.strip()
            start = offset + len(line) - len(line.lstrip())
            # Bodies and structure fields are indented; commands must be literal
            # line-leading commands. A masked column-zero doc comment may precede one.
            if not stripped:
                offset += len(line)
                continue
            if raw[:len(raw) - len(raw.lstrip())]:
                require(not SCOPE.match(stripped) and not DECL.match(stripped) and not UNSUPPORTED.match(stripped),
                        ('Indented Lean declaration/scope commands are unsupported', path, number))
                offset += len(line)
                continue
            if stripped.startswith('@['):
                pos, depth = start + 2, 1
                while pos < offset + len(line) and depth:
                    depth += (self.code[pos] == '[') - (self.code[pos] == ']')
                    pos += 1
                require(depth == 0, ('Multiline attributes are unsupported', path, number))
                attributes = start if attributes is None else attributes
                start = pos
                while start < offset + len(line) and self.code[start].isspace():
                    start += 1
                stripped = self.code[start:offset + len(line)].strip()
                if not stripped:
                    offset += len(line)
                    continue
                require(not stripped.startswith('@['), ('Repeated same-line Lean attributes are unsupported', path, number))
            require(not UNSUPPORTED.match(stripped), ('Unsupported Lean command in current-source lookup', path, number, stripped[:80]))
            command_start = attributes if attributes is not None else start
            if scope := SCOPE.fullmatch(stripped):
                require(attributes is None, ('Attributes on a Lean scope command are unsupported', path, number))
                kind, label = scope.groups()
                if kind == 'namespace':
                    require(label, ('Anonymous namespace is unsupported', path, number))
                    require(label != '_root_', ('Bare _root_ namespace is unsupported; use _root_.Name', path, number))
                    scopes.append(('namespace', label, namespace[:]))
                    namespace = label.removeprefix('_root_.').split('.') if label.startswith('_root_.') else namespace + label.split('.')
                elif kind.endswith('section'):
                    scopes.append(('section', label, namespace[:]))
                else:
                    require(scopes, ('Unmatched Lean scope end', path, number))
                    _, opened, previous = scopes.pop()
                    require(label is None or label == opened or (opened or '').endswith('.' + label),
                            ('Mismatched Lean scope end', path, number, opened, label))
                    namespace = previous
                commands.append(command_start)
            elif decl := DECL.match(stripped):
                commands.append(command_start)
                name = decl['name']
                qualified = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(namespace + [name])
                require(qualified not in self.entries, ('Duplicate lexical Lean declaration', path, qualified))
                self.entries[qualified] = {'path': path, 'line': self.code[:command_start].count('\n') + 1,
                                           'kind': decl['kind'], 'private': 'private' in decl['mods'].split(),
                                           'start': command_start, 'header_start': start + decl.end()}
            elif COMMAND.match(stripped) or re.match(r'(?:noncomputable\s+)?instance\s*[:\[(]', stripped):
                require(not re.search(r'\b(namespace|section|end)\b', stripped),
                        ('Inline or wrapped Lean scope commands are unsupported', path, number))
                commands.append(command_start)
            elif re.match(r'(namespace|section|end|theorem|lemma|def|abbrev|structure|class|instance|opaque|axiom)\b', stripped):
                raise SourceError(('Unsupported Lean command spelling', path, number, stripped[:100]))
            elif re.match(r'[^\W\d]', stripped) and not re.match(r'(by|where|deriving|termination_by|decreasing_by)\b', stripped):
                raise SourceError(('Unknown column-zero Lean command or unindented continuation', path, number, stripped[:100]))
            attributes = None
            offset += len(line)
        require(attributes is None, ('Unattached Lean attribute', path))
        self.commands = commands + [len(text)]

    def declaration(self, name):
        entry = self.entries[name]
        require(not entry['private'], ('Private declaration is not a public cited name', name, self.path))
        start = entry['start']
        end = next(pos for pos in self.commands if pos > start)
        if entry['kind'] in {'theorem', 'lemma'}:
            end = header_end(self.code, entry['header_start'], end, name)
            require(':' in self.code[entry['header_start']:end], ('Lean result needs an explicit complete type', name))
        else:
            # Include the whole definition/structure, not an 80-line prefix or
            # just a type. Trailing comments for the next command are not its body.
            end = start + len(code_mask(self.text[start:end], preserve_literals=True).rstrip())
        return {k: entry[k] for k in ('path', 'line', 'kind')} | {'statement': self.text[start:end].strip()}


class Sources:
    """Inventory literal declarations; unsupported unrelated files are not evidence."""
    def __init__(self, root, paths):
        self.root, self.modules, self.errors, self.names = Path(root), {}, {}, {}
        for path in paths:
            relative = path.relative_to(self.root).as_posix()
            try:
                require(path.resolve().is_relative_to(self.root.resolve()), ('Escaping Lean source', relative))
                module = Module(relative, path.read_text())
                self.modules[relative] = module
                for name in module.entries:
                    self.names.setdefault(name, []).append(relative)
            except SourceError as error:
                self.errors[relative] = error

    def names_in_file(self, path):
        relative = Path(path).relative_to(self.root).as_posix()
        module = self.modules.get(relative)
        return {n for n, e in module.entries.items() if not e['private']} if module else set()

    def get(self, name, expected=None):
        if expected in self.errors:
            raise self.errors[expected]
        paths = self.names.get(name, [])
        public = [p for p in paths if not self.modules[p].entries[name]['private']]
        require(public or not paths, ('Private declaration is not a public cited name', name, paths))
        paths = public
        require(len(paths) == 1, ('Unresolved or ambiguous public lexical Lean name', name, paths))
        return self.modules[paths[0]].declaration(name)
