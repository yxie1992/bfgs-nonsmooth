#!/usr/bin/env python3
"""Verify the saved M44 checkpoint assets; optionally check the paused worktree.

--working-tree is intended before resumption. Once M44 resumes, intentional
source changes will no longer match those paused-source fingerprints.
"""
from pathlib import Path
import argparse
import hashlib
import json


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--working-tree', action='store_true')
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[2]
    root = next(p for p in base.parents if (p / 'editorial/lean_coverage/resync_register.py').is_file())
    manifest = json.loads((base / 'checkpoint/MANIFEST.json').read_text())
    failures = []
    for record in manifest['files']:
        path = base / record['path']
        if digest(path) != record['sha256']:
            failures.append('asset: ' + record['path'])
    print('Saved assets checked:', len(manifest['files']))
    if args.working_tree:
        state = json.loads((base / 'checkpoint/STATE.json').read_text())
        for record in state['paused_working_files']:
            if digest(root / record['path']) != record['sha256']:
                failures.append('working file: ' + record['path'])
        print('Paused working files checked:', len(state['paused_working_files']))
    for failure in failures:
        print('MISSING OR CHANGED', failure)
    print('PASS' if not failures else 'FAIL')
    raise SystemExit(0 if not failures else 1)


if __name__ == '__main__':
    main()
