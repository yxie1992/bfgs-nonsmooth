#!/usr/bin/env python3
"""Validate the closed fifteenth gate, delivered-only scopes and source record."""
import ast
import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd).decode().strip()


s = json.loads((ROOT / 'audit/STATUS.json').read_text())
assert s['status'] == 'MODULE_M_AND_REPORT_ALGEBRA_COMPLETION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
assert not s['remaining_target_obligations']
assert s['static_scan_passed'] and s['lean_typechecking_performed']
hashes = json.loads((ROOT / 'audit/report_algebra_completion_source_hashes.json').read_text())
assert len(hashes) == 633
for f, h in hashes.items():
    assert hashlib.sha256((ROOT / f).read_bytes()).hexdigest() == h, f
all_sources = {str(p.relative_to(ROOT)) for p in (ROOT / 'BfgsVerification').glob('*.lean')}
all_sources |= {'BfgsVerification.lean', 'Audit.lean'}
assert all_sources == set(hashes)

# Read registered literal targets without importing or running check.py again.
targets = {}
for node in ast.parse((ROOT / 'scripts/check.py').read_text()).body:
    if isinstance(node, ast.Assign) and isinstance(node.value, ast.Dict):
        if any(isinstance(t, ast.Name) and (t.id == 'TARGETS' or t.id.endswith('_TARGETS'))
               for t in node.targets):
            targets.update(ast.literal_eval(node.value))
assert len(targets) == 205, len(targets)
assert all(s[flag] for flag in targets)
inventory = {x['theorem']: x for x in json.loads((ROOT / 'audit/declarations.json').read_text())}
assert len(inventory) == s['audited_declaration_count']
for name, signature in targets.values():
    assert inventory[name]['signature'] == signature, name
for row in inventory.values():
    assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, row['theorem']

packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
assert len(packages) == 9
for package in packages:
    at = ROOT / '.lake/packages' / package['name']
    assert command(['git', 'rev-parse', 'HEAD'], at) == package['rev'], package['name']
    assert not command(['git', 'status', '--porcelain'], at), package['name']
original = [f for f in command(['git', 'ls-tree', '-r', '--name-only', '2c8bb60'], REPO).splitlines()
            if not f.startswith('bfgs_lean_stage1/')]
assert len(original) == 22
for f in original:
    assert (REPO / f).read_bytes() == subprocess.check_output(
        ['git', 'show', '2c8bb60:' + f], cwd=REPO), f

for prefix in ['sign_query', 'positive_index', 'd_source_supplement', 'semialgebraic_projection']:
    assert 'PASS' in command(['python3', 'scripts/verify_report_sign_query_scoped.py',
                             '--validate-only', '--manifest', f'audit/{prefix}_declarations.json'])
for generator in ['audit/generate_d_displays.py', 'audit/generate_d_auxiliary.py']:
    assert 'PASS' in command(['python3', generator, '--check'])
for name in ['REPORT_ALGEBRA_COMPLETION_STATEMENT_REVIEW.md', 'I_SOURCE_RECONCILIATION.md',
             'HISTORICAL_EVIDENCE_RECONCILIATION.md']:
    assert (ROOT / 'audit' / name).is_file(), name
r = json.loads((ROOT / 'audit/REPORT_STATUS.json').read_text())
assert not r['entire_report_verified']
m = next(m for m in r['milestones'] if m['id'] == 'report_algebra_completion_15')
assert m['exact_targets'] == 205
assert m['explicit_theorems'] == len(s['verified_declarations'])
assert m['audited_theorems'] == s['audited_declaration_count']
for module in r['modules']:
    source = REPO / module['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == module['source_sha256']
    if module['module'] in ['I', 'E']:
        assert all(row['claim_review'] != 'pending' for row in module['coverage_spans'])
        # These are read/reconciled spans; historical/remaining mathematical
        # obligations remain unverified rather than being marked complete.
    for row in module['coverage_spans']:
        for name in row.get('verified_exports', []):
            assert name in inventory, name
print(dt.datetime.now(dt.timezone.utc).isoformat())
print(f'PASS: {len(s["verified_declarations"])} explicit/{s["audited_declaration_count"]} '
      'total theorem declarations;205 actual exact targets;633 unchanged Lean hashes.')
print('PASS: four delivered-only scoped source/type/axiom/contract gates and peer records;'
      ' byte-identical D candidate regeneration;9 exact clean dependency commits;'
      '22 unchanged original research artifacts.')
print('PASS: I/E exhaustive source reconciliation; A finite path/value and C consequence,'
      ' D literal wrappers and historical evidence remain explicit; entire_report_verified=false.')
