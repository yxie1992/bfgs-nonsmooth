#!/usr/bin/env python3
"""Read-only adverse-input tests; overlays never mutate proof/cache/evidence files."""
from pathlib import Path
import copy
import importlib.util
import json
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[5]
spec = importlib.util.spec_from_file_location('cache_binding', ROOT / 'editorial/satisfaction_review/cache_binding.py')
binding = importlib.util.module_from_spec(spec)
spec.loader.exec_module(binding)
MP = ROOT / 'editorial/satisfaction_review/cache_binding/runs/cache_binding_04/MANIFEST.json'
manifest = json.loads(MP.read_text())
CP = ROOT / manifest['run_directory'] / 'commands.json'
commands = json.loads(CP.read_text())
original_read_text = Path.read_text
results = []


def expect(label, action, fragment):
    try:
        action()
    except RuntimeError as error:
        if fragment not in str(error):
            raise RuntimeError(label + ': wrong rejection: ' + str(error))
        results.append({'case': label, 'status': 'REJECTED_AS_EXPECTED', 'reason': str(error)})
    else:
        raise RuntimeError(label + ': false PASS')


def overlay(path, value, action):
    def read(self, *args, **kwargs):
        return json.dumps(value) if self == path else original_read_text(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        return action()


binding.check_receipts(ROOT, manifest)
results.append({'case': 'Unchanged actual command receipts', 'status': 'PASS'})
bad = copy.deepcopy(commands)
bad[0]['exit_code'] = 1
expect('Failed command with retained success-looking logs',
       lambda: overlay(CP, bad, lambda: binding.check_receipts(ROOT, manifest)), 'Wrong/failed binding command')
bad = copy.deepcopy(commands)
next(c for c in bad if c['command'][-2:] == ['build', 'BfgsVerification'])['command'].insert(-2, '--no-build')
expect('Different actual build command',
       lambda: overlay(CP, bad, lambda: binding.check_receipts(ROOT, manifest)), 'Wrong/failed binding command')
bad = copy.deepcopy(manifest)
bad['search_directories'] = [p for p in bad['search_directories'] if '/.toolchain/' not in p]
expect('Dropped built-in standard-library search entry', lambda: binding.check_receipts(ROOT, bad), 'Search-path receipt disagrees')
bad = copy.deepcopy(manifest)
bad['objects'].pop(next(iter(bad['objects'])))
expect('Omitted object from sealed inventory', lambda: binding.check_receipts(ROOT, bad), 'Object hash input list differs')
rows = json.loads((ROOT / manifest['run_directory'] / 'before_validate_object_hashes.stdout.log').read_text())
next(r for r in rows['objects'] if r['hash_sidecar_present'])['actual_lake_binary_hash'] = '0'
expect('Mismatched independently computed binary hash',
       lambda: binding.check_output_hash_result(ROOT, json.dumps(rows), manifest['objects']), 'Stale cached output hash')
bad = copy.deepcopy(manifest)
bad['successful_rehash_build'] = True
expect('Invented successful rehash scope', lambda: overlay(MP, bad, lambda: binding.check_manifest(ROOT, MP)), 'Incorrect cache evidence scope')
bad = copy.deepcopy(manifest)
target = 'bfgs_lean_stage1/.lake/build/lib/lean/BfgsVerification.olean'
bad['cache_files'][target]['sha256'] = '0' * 64
expect('Changed cached-object SHA256 expectation',
       lambda: overlay(MP, bad, lambda: binding.check_manifest(ROOT, MP)), 'Cached object/source/trace bytes differ')
output = {'status': 'PASS', 'scope': 'Read-only adverse manifest/log overlays against actual cache04 evidence; no proof, cache or retained evidence file was changed.',
          'manifest_sha256': binding.sha(MP), 'helper_sha256': binding.sha(ROOT / binding.SCRIPT_REL), 'checks': results}
(Path(__file__).parent / 'GUARD_TESTS.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
