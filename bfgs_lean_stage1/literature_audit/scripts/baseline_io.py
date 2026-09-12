"""Read the exact audited report edition, including after an authorized revision.

The original BASELINE.json hashes remain authoritative. Git fallback reads only
that explicitly recorded historical commit and checks the bytes before use.
"""
import functools
import hashlib
import json
from pathlib import Path
import re
import subprocess

if not __debug__:
    raise RuntimeError('Run without Python optimization; baseline assertion checks must be enabled.')

BASE=Path(__file__).resolve().parents[1]
REPO=BASE.parents[1]
SPEC=json.loads((BASE/'BASELINE.json').read_text())
LOCATIONS={}

@functools.lru_cache(maxsize=None)
def baseline_bytes(name):
    path=Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    assert name in SPEC['files'], ('Unrecorded baseline path',name)
    expected=SPEC['files'][name]
    current=REPO/name
    current_bytes=current.read_bytes() if current.is_file() else None
    if current_bytes is not None and hashlib.sha256(current_bytes).hexdigest()==expected:
        LOCATIONS[name]='current_checkout'
        return current_bytes
    commit=SPEC['source_commit']
    assert re.fullmatch(r'[0-9a-f]{40}',commit)
    result=subprocess.run(['git','show',commit+':'+name],cwd=REPO,capture_output=True)
    if result.returncode:
        raise RuntimeError('The audited historical commit is required: '+commit+'. Restore/fetch that Git history; do not replace the baseline hashes.')
    assert hashlib.sha256(result.stdout).hexdigest()==expected, ('Historical baseline hash mismatch',name)
    LOCATIONS[name]='git:'+commit
    return result.stdout

def baseline_json(name):
    return json.loads(baseline_bytes(name))
