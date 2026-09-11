#!/usr/bin/env python3
"""Validate the closed eighteenth gate, delivered-only scopes and source record."""
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
assert s['status'] == 'MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
assert not s['remaining_target_obligations']
assert s['static_scan_passed'] and s['lean_typechecking_performed']
hashes = json.loads((ROOT / 'audit/report_literal_foundation_source_hashes.json').read_text())
assert len(hashes) == 729
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
assert len(targets) == 251, len(targets)
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

for prefix in ['sign_query', 'positive_index', 'd_source_supplement', 'semialgebraic_projection', 'tame_geometry', 'd_literal_closure', 'boundary_sign', 'general_smooth_cover', 'critical_geometry', 'semialgebraic_path_completion', 'module_m_literal_completion']:
    assert 'PASS' in command(['python3', 'scripts/verify_report_sign_query_scoped.py',
                             '--validate-only', '--manifest', f'audit/{prefix}_declarations.json'])
for validator in ['audit/validate_smooth_components.py', 'audit/validate_semialgebraic_smooth_components.py', 'scripts/validate_d_literal_closure.py']:
    assert 'PASS' in command(['python3', validator])
assert 'PASS' in command(['python3', 'audit/validate_semialgebraic_path_completion_provenance.py'])
assert 'PASS' in command(['python3', 'scripts/validate_semialgebraic_path_source_map.py', '--require-central'])
assert 'PASS' in command(['python3', 'audit/validate_module_m_literal_completion_provenance.py'])
assert 'PASS' in command(['python3', 'scripts/validate_module_m_literal_source_map.py'])
assert 'PASS' in command(['python3', 'scripts/validate_cached_axiom_audit.py'])
for generator in ['audit/generate_d_displays.py', 'audit/generate_d_auxiliary.py']:
    assert 'PASS' in command(['python3', generator, '--check'])
for name in ['REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md', 'I_SOURCE_RECONCILIATION.md',
             'HISTORICAL_EVIDENCE_RECONCILIATION.md']:
    assert (ROOT / 'audit' / name).is_file(), name
r = json.loads((ROOT / 'audit/REPORT_STATUS.json').read_text())
assert not r['entire_report_verified']
m = next(m for m in r['milestones'] if m['id'] == 'report_literal_foundation_18')
assert m['exact_targets'] == 251
assert m['explicit_theorems'] == len(s['verified_declarations'])
assert m['audited_theorems'] == s['audited_declaration_count']
modules={m['module']:m for m in r['modules']}
assert not modules['D']['remaining_claims']
assert not modules['A']['remaining_claims']
assert not modules['C']['remaining_claims']
assert not modules['M']['remaining_claims']
assert 'older' in modules['R']['remaining_claims']
assert 'Historical' in modules['E']['remaining_claims']
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
      'total theorem declarations;251 actual exact targets;729 unchanged Lean hashes.')
print('PASS: delivered-only scoped source/type/axiom/contract gates and peer records;'
      ' byte-identical D candidate regeneration;9 exact clean dependency commits;'
      '22 unchanged original research artifacts.')
print('PASS: exhaustive source reconciliation; actual A/I finite-value and C basin conclusions, D literal closure; all literal A/C path/composition claims closed; M literal identities complete; historical/source-attribution exceptions explicit; entire_report_verified=false.')
