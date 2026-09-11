#!/usr/bin/env python3
from pathlib import Path
import datetime
import hashlib
import json
import re

base = Path(__file__).resolve().parent
manifest = json.loads((base / 'declarations.json').read_text())
for source in manifest['sources']:
    assert hashlib.sha256((base / source['path']).read_bytes()).hexdigest() == source['sha256']
log = (base / 'axioms_contracts.log').read_text()
assert 'error:' not in log
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
assert len(reports) == len(manifest['declarations']) == 25
assert {name for name, _ in reports} == set(manifest['declarations'])
for name, axioms in reports:
    assert set(axioms.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}, name
assert re.findall(r'^EXACT_TARGET_OK (\S+)$', log, re.M) == [p[0] for p in manifest['targets']]
for name in ['build.log', 'targets_build.log']:
    assert 'error:' not in (base / name).read_text()
result = datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n'
result += 'PASS:2 frozen sources;25 actual type/ordinary transitive axiom reports;1 strict complete target;no unexpected axioms.\n'
(base / 'validation.log').write_text(result)
print(result, end='')
