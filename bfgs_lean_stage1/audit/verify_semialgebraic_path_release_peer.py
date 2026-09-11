#!/usr/bin/env python3
"""Read-only release preflight; does not run the updater or the full validator.

Exercise their public subordinate validators with excluded-input reads blocked.
This checks delivery tooling, not completion of the separate full central audit.
"""
from pathlib import Path
import ast
import datetime
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / 'audit'
PROGRAM = '''import pathlib,runpy,sys
root=pathlib.Path.cwd()
def guard(event,args):
 if event=="open" and isinstance(args[0],(str,bytes)):
  path=pathlib.Path(args[0]).resolve()
  if path.is_relative_to(root/"audit/scratch") or path.is_relative_to(root/".scratch"):
   raise RuntimeError("EXCLUDED_INPUT_READ: "+str(path))
sys.addaudithook(guard)
sys.argv=sys.argv[1:]
runpy.run_path(sys.argv[0],run_name="__main__")
'''

commands = [
    ['scripts/verify_report_sign_query_scoped.py', '--validate-only', '--manifest',
     f'audit/{prefix}_declarations.json']
    for prefix in ['sign_query', 'positive_index', 'd_source_supplement',
                   'semialgebraic_projection', 'tame_geometry', 'd_literal_closure',
                   'boundary_sign', 'general_smooth_cover', 'critical_geometry',
                   'semialgebraic_path_completion']
]
commands += [[p] for p in [
    'audit/validate_smooth_components.py', 'audit/validate_semialgebraic_smooth_components.py',
    'scripts/validate_d_literal_closure.py',
    'audit/validate_semialgebraic_path_completion_provenance.py',
    'scripts/report_inventory.py',
    'scripts/validate_semialgebraic_path_source_map.py',
]]
commands += [[p, '--check'] for p in [
    'audit/generate_d_displays.py', 'audit/generate_d_auxiliary.py']]

manifest = json.loads((AUDIT / 'semialgebraic_path_completion_declarations.json').read_text())
sources = [r for scope in manifest['scopes'] for r in scope['sources']]
assert len(sources) == len({r['path'] for r in sources}) == 33
assert len(manifest['declarations']) == len(set(manifest['declarations'])) == 152
assert len(manifest['targets']) == 16
frozen = json.loads((AUDIT / 'report_semialgebraic_path_source_hashes.json').read_text())
assert len(frozen) == 726
for p, expected in frozen.items():
    assert hashlib.sha256((ROOT / p).read_bytes()).hexdigest() == expected, p
files = {str(p.relative_to(ROOT)) for p in (ROOT / 'BfgsVerification').glob('*.lean')}
assert files | {'Audit.lean', 'BfgsVerification.lean'} == set(frozen)
code = (ROOT / 'scripts/check.py').read_text()
targets = {}
for node in ast.parse(code).body:
    if isinstance(node, ast.Assign) and isinstance(node.value, ast.Dict):
        if any(isinstance(t, ast.Name) and (t.id == 'TARGETS' or t.id.endswith('_TARGETS'))
               for t in node.targets):
            d = ast.literal_eval(node.value)
            assert not (targets.keys() & d.keys())
            targets.update(d)
assert len(targets) == 249
assert set(map(tuple, manifest['targets'])) <= set(targets.values())
assert 'status[flag] = name in inventory and inventory[name]["signature"] == signature' in code
assert 'default=7200' in code
for p in ['scripts/update_report_semialgebraic_path_17.py',
          'scripts/validate_report_semialgebraic_path_17.py']:
    ast.parse((ROOT / p).read_text())

with (AUDIT / 'semialgebraic_path_release_peer_validation.log').open('w') as log:
    log.write(datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
    log.write('PASS: 33/152/16 delivered manifest; 249 registered target pairs; '
              '726 current source hashes; actual-type equality and timeout7200 retained.\n')
    for cmd in commands:
        log.write('PUBLIC_COMMAND ' + json.dumps(cmd) + '\n')
        log.flush()
        result = subprocess.check_output([sys.executable, '-c', PROGRAM, *cmd],
                                         cwd=ROOT, text=True, stderr=subprocess.STDOUT)
        assert 'PASS' in result, cmd
        log.write(result)
        log.flush()
    log.write('PASS: all 18 subordinate public validator/regeneration invocations with '
              'audit/scratch and .scratch reads forbidden. Updater and full release '
              'validator were not executed; this is not a central-audit PASS.\n')
print('PASS: release tooling preflight and 18 delivered-only subordinate checks; '
      'central gate remains separately recorded.')
