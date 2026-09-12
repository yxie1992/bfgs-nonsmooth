"""Resolve the actual LaTeX input graph; ignore archived and unused sources."""
from pathlib import Path
import re


def sources(root: Path, document='paper'):
    base = root / document
    found = []
    visiting = set()

    def visit(path):
        path = path.resolve()
        if path in visiting:
            raise RuntimeError('Cyclic LaTeX input: ' + str(path))
        if path in found:
            return
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            raise RuntimeError('Missing or escaping LaTeX input: ' + str(path))
        visiting.add(path)
        found.append(path)
        text = re.sub(r'(?m)(?<!\\)%.*$', '', path.read_text())
        for name in re.findall(r'\\(?:input|include)\{([^}]+)\}', text):
            target = base / name
            if not target.suffix:
                target = target.with_suffix('.tex')
            visit(target)
        visiting.remove(path)

    visit(base / 'master.tex')
    return found
