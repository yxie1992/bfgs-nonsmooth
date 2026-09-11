#!/usr/bin/env python3
"""Independent public-only source/status review after the closed release18 gate.

This does not rerun the updater or review/approve the cached graph algorithm.
It validates actual final counts, source preservation, public proof evidence,
source-map references and the current release documentation.
"""
from pathlib import Path
import ast
import datetime
import hashlib
import json
import re
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

s = json.loads((AUDIT / 'STATUS.json').read_text())
assert s['status'] == 'MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
assert not s['remaining_target_obligations']
rows = json.loads((AUDIT / 'declarations.json').read_text())
inventory = {row['theorem']: row for row in rows}
assert len(rows) == len(inventory) == s['audited_declaration_count']
for row in rows:
    assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
code = (ROOT / 'scripts/check.py').read_text()
targets = {}
for node in ast.parse(code).body:
    if isinstance(node, ast.Assign) and isinstance(node.value, ast.Dict):
        if any(isinstance(t, ast.Name) and (t.id == 'TARGETS' or t.id.endswith('_TARGETS'))
               for t in node.targets):
            d = ast.literal_eval(node.value)
            assert not targets.keys() & d.keys()
            targets.update(d)
assert len(targets) == 251
for flag, (name, signature) in targets.items():
    assert s[flag] and inventory[name]['signature'] == signature
assert 'status[flag] = name in inventory and inventory[name]["signature"] == signature' in code
assert 'default=7200' in code
hashes = json.loads((AUDIT / 'report_literal_foundation_source_hashes.json').read_text())
assert len(hashes) == 729
assert {str(p.relative_to(ROOT)) for p in (ROOT / 'BfgsVerification').glob('*.lean')} | {'BfgsVerification.lean', 'Audit.lean'} == set(hashes)
for path, digest in hashes.items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest
r = json.loads((AUDIT / 'REPORT_STATUS.json').read_text())
assert r['entire_report_verified'] is False
modules = {m['module']: m for m in r['modules']}
assert len(modules) == 14 and not modules['M']['remaining_claims']
assert 'older' in modules['R']['remaining_claims']
assert 'Historical' in modules['E']['remaining_claims']
span_count = line_count = 0
for module in modules.values():
    raw = (ROOT.parent / module['source']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == module['source_sha256']
    spans = module['coverage_spans']
    count = len(raw.decode().splitlines())
    assert [n for row in spans for n in range(row['start_line'], row['end_line'] + 1)] == list(range(1, count + 1))
    span_count += len(spans)
    line_count += count
    for row in spans:
        assert set(row.get('verified_exports', [])) <= set(inventory)
assert (span_count, line_count) == (172, 4323)
m = next(m for m in r['milestones'] if m['id'] == 'report_literal_foundation_18')
e, a = len(s['verified_declarations']), s['audited_declaration_count']
assert (m['explicit_theorems'], m['audited_theorems'], m['exact_targets']) == (e, a, 251)
for path in ['README.md', 'audit/REPORT_VERIFICATION_OVERVIEW.md']:
    body = (ROOT / path).read_text()
    assert f'{e:,}' in body and f'{a:,}' in body and '251' in body
    assert 'report_literal_foundation_check.log' in body
    assert 'REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md' in body
body = (ROOT / 'PROOF_OBLIGATIONS.md').read_text()
assert "The source's combinatorial equality is not separately exported." not in body
assert 'principalGramSumIdentity' in body and 'Eighteenth milestone' in body
for path in ['audit/REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md',
             'audit/MODULE_M_LITERAL_SOURCE_REVIEW.md',
             'audit/MODULE_M_LITERAL_INDEPENDENT_PEER_REVIEW.md',
             'audit/MODULE_M_POTENTIAL_INDEPENDENT_PEER_REVIEW.md',
             'audit/module_m_delivery_reviews/MODULE_M_DELIVERY_INDEPENDENT_PEER_REVIEW.md']:
    assert (ROOT / path).is_file(), path
commands = [
    ['scripts/verify_report_sign_query_scoped.py', '--validate-only', '--manifest', 'audit/module_m_literal_completion_declarations.json'],
    ['audit/validate_module_m_literal_completion_provenance.py'],
    ['scripts/validate_module_m_literal_source_map.py'],
    ['scripts/validate_semialgebraic_path_source_map.py', '--require-central'],
]
with (AUDIT / 'literal_foundation_release_peer_validation.log').open('w') as log:
    log.write(datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
    for cmd in commands:
        log.write('PUBLIC_COMMAND ' + json.dumps(cmd) + '\n'); log.flush()
        result = subprocess.check_output([sys.executable, '-c', PROGRAM, *cmd],
                                         cwd=ROOT, text=True, stderr=subprocess.STDOUT)
        assert 'PASS' in result, cmd
        log.write(result); log.flush()
    log.write(f'PASS: actual {e} explicit/{a} total/251 exact targets;729 frozen sources;14 modules/172 spans/4323 unchanged source lines.\n')
    log.write('PASS: final current documents and M closure; original R/E exceptions retained; entire_report_verified=false. Public source/provenance validators used no scratch input. Cached algorithm review remains separate.\n')
print('PASS: independent final source/status/docs review with four public-only validator invocations.')
