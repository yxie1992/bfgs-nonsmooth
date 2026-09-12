#!/usr/bin/env python3
"""Restore the bundled release history in a fresh, unmodified ZIP extraction."""
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    if (root / '.git').exists():
        raise SystemExit('Git metadata already exists; no existing repository was changed.')
    inventory = json.loads((root / '_archive/CONTENTS.json').read_text())
    for name, record in inventory['files'].items():
        path = Path(name)
        if path.is_absolute() or '..' in path.parts:
            raise SystemExit('Invalid archive inventory path: ' + name)
        candidate = root / path
        if candidate.is_symlink() or not candidate.is_file():
            raise SystemExit('Missing or nonregular archive file: ' + name)
        if hashlib.sha256(candidate.read_bytes()).hexdigest() != record['sha256']:
            raise SystemExit('Archive file changed: ' + name)
    commit = inventory['source_commit']
    bundle = root / '_archive/history.bundle'
    commands = [
        ['git', 'init', '-q'],
        ['git', 'bundle', 'verify', str(bundle)],
        ['git', 'fetch', '-q', '--no-tags', str(bundle), 'HEAD'],
        ['git', 'symbolic-ref', 'HEAD', 'refs/heads/main'],
        ['git', 'reset', '-q', '--mixed', commit],
    ]
    for command in commands:
        subprocess.run(command, cwd=root, check=True)
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    if actual != commit:
        raise SystemExit('Restored history has the wrong release commit.')
    print('Restored release history at ' + commit + '; source files were not overwritten.')


if __name__ == '__main__':
    main()
