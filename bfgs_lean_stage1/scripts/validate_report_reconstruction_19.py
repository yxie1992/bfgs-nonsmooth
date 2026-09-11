#!/usr/bin/env python3
"""Validate the actual nineteenth build and the explicitly corrected report.

--core-only checks the completed mathematical build without claiming report
completion. --pre-promotion additionally checks the new execution evidence.
The default also requires the final corrected-source register and companion.
No excluded authoring directory is a runtime input.
"""
import argparse
import ast
import datetime as dt
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BASE = '19c76918cb790c311157c85777aa24a76f185b05'


def path(rel, root=ROOT):
    rel = PurePosixPath(rel)
    assert not rel.is_absolute() and '..' not in rel.parts
    p = root.joinpath(*rel.parts).resolve()
    assert p.is_relative_to(root.resolve())
    assert not p.is_relative_to(ROOT / 'audit/scratch')
    return p


def data(rel):
    return json.loads(path(rel).read_text())


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def registry(code):
    out = {}
    for node in ast.parse(code).body:
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Dict):
            if any(isinstance(t, ast.Name) and
                   (t.id == 'TARGETS' or t.id.endswith('_TARGETS')) for t in node.targets):
                rows = ast.literal_eval(node.value)
                assert not out.keys() & rows.keys()
                out.update(rows)
    return out


def core():
    s = data('audit/STATUS.json')
    assert s['status'] == 'MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED'
    assert s['static_scan_passed'] and s['lean_typechecking_performed']
    assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
    assert not s['remaining_target_obligations']
    assert not s['entire_report_verified']  # Core evidence alone is not source reconciliation.
    frozen = data('audit/report_reconstruction_source_hashes.json')
    assert len(frozen) == 737
    actual = {str(p.relative_to(ROOT)) for p in (ROOT / 'BfgsVerification').glob('*.lean')}
    assert actual | {'BfgsVerification.lean', 'Audit.lean'} == set(frozen)
    for rel, h in frozen.items():
        assert digest(path(rel)) == h, rel
    old = data('audit/report_literal_foundation_source_hashes.json')
    assert len(old) == 729
    for rel, h in old.items():
        if rel not in {'Audit.lean', 'BfgsVerification.lean'}:
            assert frozen[rel] == h, rel
    reg = data('audit/reconstruction_completion_registration.json')
    for rel, key in [('scripts/check.py', 'check_sha256'),
                     ('Audit.lean', 'registered_audit_sha256'),
                     ('BfgsVerification.lean', 'root_sha256')]:
        assert digest(path(rel)) == reg[key], rel
    amendment = data('audit/reconstruction_status_wording_amendment.json')
    assert amendment['proof_or_criterion_change'] is False
    assert amendment['checker_after_sha256'] == reg['check_sha256']
    checker = path('scripts/check.py').read_text()
    assert checker.count(amendment['after']) == 1
    restored = checker.replace(amendment['after'], amendment['before'], 1)
    assert hashlib.sha256(restored.encode()).hexdigest() == amendment['checker_before_sha256']
    assert digest(path('audit/report_reconstruction_initial_check.log')) == amendment['first_full_check_sha256']
    assert digest(path('audit/report_reconstruction_initial_core_validation.log')) == amendment['first_core_validation_sha256']
    assert digest(path('audit/report_reconstruction_source_hashes.json')) == amendment['proof_source_freeze_sha256']
    previous_audit = path('audit/cached_axiom_evidence/ProposedCurrentAudit.lean').read_bytes()
    assert hashlib.sha256(previous_audit).hexdigest() == old['Audit.lean']
    assert path('Audit.lean').read_bytes().startswith(previous_audit)
    targets = registry(path('scripts/check.py').read_text())
    assert len(targets) == 255 and all(s[flag] for flag in targets)
    old_code = command(['git', 'show', BASE + ':bfgs_lean_stage1/scripts/check.py'], REPO)
    old_targets = registry(old_code)
    assert len(old_targets) == 251 and all(targets[k] == v for k, v in old_targets.items())
    rows = data('audit/declarations.json')
    inventory = {x['theorem']: x for x in rows}
    assert len(rows) == len(inventory) == s['audited_declaration_count']
    assert len(s['verified_declarations']) == s['explicit_theorem_declarations']
    for name, sig in targets.values():
        assert inventory[name]['signature'] == sig, name
    for row in rows:
        assert set(row['axioms']) <= ALLOWED, row['theorem']
    prior = {x['theorem']: x for x in data('audit/cached_axiom_evidence/current_cached_reports.json')
             if x['isTheorem']}
    assert len(prior) == 7704
    for name, row in prior.items():
        assert inventory[name]['signature'] == row['signature'], name
        assert set(inventory[name]['axioms']) == set(row['axioms']), name
    manifest = data('audit/reconstruction_completion_declarations.json')
    assert len(manifest['declarations']) == 85 and len(manifest['targets']) == 4
    ordinary = path('audit/reconstruction_completion_axioms_contracts.log').read_text()
    ax = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", ordinary)
    assert [n for n, _ in ax] == manifest['declarations']
    for name, axiom_text in ax:
        values = set(axiom_text.replace(',', ' ').split())
        assert values <= ALLOWED
        if name in inventory:
            assert values == set(inventory[name]['axioms']), name
    complete = path('audit/report_reconstruction_check.log').read_text()
    assert 'MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED' in complete
    assert '"remaining_target_obligations": []' in complete
    assert '"unexpected_axioms": []' in complete
    packages = data('lake-manifest.json')['packages']
    assert len(packages) == 9
    for package in packages:
        at = ROOT / '.lake/packages' / package['name']
        assert command(['git', 'rev-parse', 'HEAD'], at) == package['rev']
        assert not command(['git', 'status', '--porcelain'], at)
    originals = [f for f in command(['git', 'ls-tree', '-r', '--name-only', '2c8bb60'], REPO).splitlines()
                 if not f.startswith('bfgs_lean_stage1/')]
    assert len(originals) == 22
    for rel in originals:
        assert path(rel, REPO).read_bytes() == subprocess.check_output(
            ['git', 'show', '2c8bb60:' + rel], cwd=REPO), rel
    for prefix in ['sign_query', 'positive_index', 'd_source_supplement',
                   'semialgebraic_projection', 'tame_geometry', 'd_literal_closure',
                   'boundary_sign', 'general_smooth_cover', 'critical_geometry',
                   'semialgebraic_path_completion', 'module_m_literal_completion',
                   'reconstruction_completion']:
        assert 'PASS' in command(['python3', 'scripts/verify_report_sign_query_scoped.py',
                                 '--validate-only', '--manifest', f'audit/{prefix}_declarations.json'])
    for validator in ['audit/validate_smooth_components.py',
                      'audit/validate_semialgebraic_smooth_components.py',
                      'scripts/validate_d_literal_closure.py',
                      'audit/validate_semialgebraic_path_completion_provenance.py',
                      'audit/validate_module_m_literal_completion_provenance.py',
                      'audit/validate_reconstruction_completion_provenance.py']:
        assert 'PASS' in command(['python3', validator])
    assert 'PASS' in command(['python3', 'scripts/validate_semialgebraic_path_source_map.py', '--require-central'])
    # Revalidate the immutable M map against this new central inventory. The
    # historical milestone18 validator deliberately pins its old status label.
    m = data('audit/module_m_literal_source_map.json')
    assert digest(path('audit/module_m_literal_source_map.json')) == '55c0435d35b1e6c4f18820ebbcb36cb22047591851ecb7ba4a39cebb73de3da9'
    for rel, h in data('audit/module_m_literal_source_kinds_hashes.json').items():
        assert digest(path(rel)) == h
    names = {n for span in m['spans'] for n in span['declarations']}
    kinds = dict(re.findall(r'^M_SOURCE_KIND (\S+) (\S+)$', path('audit/module_m_literal_source_kinds.log').read_text(), re.M))
    assert len(names) == 53 and set(kinds) == names and set(kinds.values()) == {'theorem'}
    assert names <= inventory.keys()
    for generator in ['audit/generate_d_displays.py', 'audit/generate_d_auxiliary.py']:
        assert 'PASS' in command(['python3', generator, '--check'])
    print(f'PASS: {len(s["verified_declarations"])} explicit/{len(rows)} total theorems;255 exact targets;737 source hashes;all7704 prior theorem types/axioms and727 old proof sources unchanged.')
    print('PASS: ordinary85-report reconstruction comparison, delivered-only scopes, cached Audit preservation,9 exact clean dependencies and22 unchanged research originals.')
    return s, inventory


def source_register(s, inventory):
    r = data('audit/REPORT_STATUS.json')
    assert r['schema_version'] == 2
    assert not r['entire_report_verified'] and not r['original_snapshot_all_assertions_verified']
    for key in ['corrected_report_mathematics_verified', 'reconstructed_execution_evidence_verified',
                'corrected_source_reconciliation_verified', 'corrected_report_verified']:
        assert r[key] is True, key
    assert r['historical_assertions_status'] == 'superseded_unsupported_ai_generated_history'
    assert r['verification_scope']['companion'] == 'CORRECTED_REPORT.md'
    assert digest(path('CORRECTED_REPORT.md')) == r['verification_scope']['companion_sha256']
    assert 'Draft release status' not in path('CORRECTED_REPORT.md').read_text()
    modules = r['modules']
    assert len(modules) == 14 and len({m['module'] for m in modules}) == 14
    span_count = line_count = 0
    for module in modules:
        source = path(module['source'], REPO)
        assert digest(source) == module['source_sha256']
        assert module['corrected_retained_mathematics_verified'] is True
        assert not module['remaining_claims']
        spans = module['coverage_spans']
        n = len(source.read_text().splitlines())
        assert [i for row in spans for i in range(row['start_line'], row['end_line'] + 1)] == list(range(1, n + 1))
        span_count += len(spans)
        line_count += n
        for row in spans:
            assert row['claim_review'] != 'pending'
            for name in row.get('verified_exports', []):
                assert name in inventory, name
    assert (span_count, line_count) == (172, 4323)
    original_register = json.loads(command(['git', 'show', BASE + ':bfgs_lean_stage1/audit/REPORT_STATUS.json'], REPO))
    corrections = {x['id']: x for x in r['mathematical_corrections']}
    assert len(original_register['mathematical_corrections']) == 9
    for old in original_register['mathematical_corrections']:
        assert old['id'] in corrections
        if old['id'] != 'R.historical_four_piece_attribution':
            assert corrections[old['id']] == old, old['id']
        else:
            assert corrections[old['id']]['previous_record'] == old
    for old, new in zip(original_register['modules'], modules):
        assert old['module'] == new['module']
        assert old['source_sha256'] == new['source_sha256']
        assert new['previous_snapshot_status'] == old['status']
        for a, b in zip(old['coverage_spans'], new['coverage_spans']):
            for key in ['id', 'start_line', 'end_line', 'anchor', 'labels']:
                assert a[key] == b[key]
            assert set(a.get('verified_exports', [])) <= set(b.get('verified_exports', []))
    milestone = next(x for x in r['milestones'] if x['id'] == 'report_reconstruction_19')
    assert milestone['explicit_theorems'] == len(s['verified_declarations'])
    assert milestone['audited_theorems'] == len(inventory) and milestone['exact_targets'] == 255
    for rel, h in data('audit/reconstruction_final_review_hashes.json').items():
        assert digest(path(rel)) == h, rel
    review = path('audit/REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md').read_text()
    assert re.search(r'^PASS\b', review, re.M)
    print('PASS: corrected edition14 modules/172 disjoint spans/4323 lines;all previous exports and9 corrections retained;explicit reconstruction/substitution scope;original-history flags remain false.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--core-only', action='store_true')
    mode.add_argument('--pre-promotion', action='store_true')
    a = p.parse_args()
    s, inventory = core()
    if not a.core_only:
        print(command(['python3', 'verification/reconstructed/validate.py', '--validate-only']))
    if not a.core_only and not a.pre_promotion:
        source_register(s, inventory)
    print(dt.datetime.now(dt.timezone.utc).isoformat())


if __name__ == '__main__':
    main()
