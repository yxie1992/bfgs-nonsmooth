#!/usr/bin/env python3
"""Validate delivered literal source review; historical labels are never opened.

This read-only metadata/provenance check does not rerun Lean. --require-central
is mandatory for the downstream post-full-gate invocation. Before that gate,
only actual theorem names from the delivered aggregate may augment the theorem
inventory. Definitions and fields remain covered by the complete scoped audit.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path, PurePosixPath

EXPECTED_SNAPSHOT = '753c7f98972de24a8b0c0cc8d77451867b7beffda2f3b9ccf83091e04a296af0'
EXPECTED_LITERAL_ROWS = '2d4ced97d5b7e18227ed5352ab797c94b163f92d7517eb2b2a48a033aae272aa'
EXPECTED_SCOPES = {
    'semialgebraic_path_graphs': (5, 22),
    'semialgebraic_smooth_paths': (7, 41),
    'semialgebraic_path_cover': (6, 22),
    'semialgebraic_scalar_smooth': (5, 14),
    'semialgebraic_objective_composition': (3, 8),
    'critical_path_source': (2, 5),
    'semialgebraic_path_components': (5, 40),
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode()


def permitted(root, relative):
    """All input paths are project/repository-relative, with no excluded reads."""
    part = PurePosixPath(relative)
    assert not part.is_absolute() and '..' not in part.parts, relative
    assert tuple(part.parts[:2]) != ('audit', 'scratch'), relative
    path = root.joinpath(*part.parts)
    resolved = path.resolve()
    assert resolved.is_relative_to(root.resolve()), relative
    resolved_relative = resolved.relative_to(root.resolve())
    assert tuple(resolved_relative.parts[:2]) != ('audit', 'scratch'), relative
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-central', action='store_true')
    # Explicit roots permit a private delivery-tree test; production needs none.
    parser.add_argument('--project-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--repository-root', type=Path)
    args = parser.parse_args()
    root = args.project_root.resolve()
    repo = (args.repository_root or root.parent).resolve()
    read = lambda relative: permitted(root, relative).read_bytes()
    data = lambda relative: json.loads(read(relative))

    mapping = data('audit/semialgebraic_path_final_source_map.json')
    snapshot_bytes = read('audit/semialgebraic_path_reviewed_report_status.json')
    assert digest(snapshot_bytes) == EXPECTED_SNAPSHOT
    snapshot = json.loads(snapshot_bytes)
    historical = mapping['historical_review']
    assert historical['snapshot_sha256'] == EXPECTED_SNAPSHOT
    assert historical['snapshot_is_current_normative_status'] is False
    assert historical['review_stage'] == 'frozen_pre_milestone17_delivery'
    assert historical['inventory_sha256_at_review']
    assert historical['inventory_count_at_review'] == 7486
    assert digest(read(mapping['review_path'])) == mapping['review_sha256']
    assert mapping['aggregate_manifest'] == 'audit/semialgebraic_path_completion_declarations.json'
    aggregate = data(mapping['aggregate_manifest'])
    assert aggregate['historical_paths_are_provenance_only'] is True
    assert len(aggregate['declarations']) == len(set(aggregate['declarations'])) == 152
    assert len(aggregate['targets']) == 16
    scoped_names = set(aggregate['declarations'])
    assert scoped_names == set(mapping['reviewed_candidate_declarations'])
    kind = mapping['actual_declaration_kinds']
    assert digest(read(kind['driver'])) == kind['driver_sha256']
    kind_bytes = read(kind['log'])
    assert digest(kind_bytes) == kind['log_sha256']
    kind_text = kind_bytes.decode()
    assert 'error:' not in kind_text
    reports = re.findall(r'^DECL_KIND (\S+) isTheorem=(true|false)$', kind_text, re.M)
    assert len(reports) == len(dict(reports)) == 152
    assert set(dict(reports)) == scoped_names
    theorem_names = {name for name, value in reports if value == 'true'}
    non_theorems = scoped_names - theorem_names
    assert len(theorem_names) == 115 and len(non_theorems) == 37
    assert theorem_names == set(kind['theorem_declarations'])
    assert non_theorems == set(kind['non_theorem_declarations'])
    assert {name for name, _ in aggregate['targets']} <= theorem_names
    scoped_log = read('audit/semialgebraic_path_completion_axioms_contracts.log').decode()
    assert 'error:' not in scoped_log
    axiom_reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", scoped_log)
    assert len(axiom_reports) == 152 and {name for name, _ in axiom_reports} == scoped_names
    for name, axioms in axiom_reports:
        assert set(axioms.replace(',', ' ').split()) <= ALLOWED_AXIOMS, name
    assert len(re.findall(r'^EXACT_TARGET_OK ', scoped_log, re.M)) == 16
    assert 'error:' not in read('audit/semialgebraic_path_completion_build.log').decode()

    scopes = {s['id']: s for s in aggregate['scopes']}
    mapped_scopes = {s['scope']: s for s in mapping['reviewed_candidate_scopes']}
    assert len(scopes) == len(aggregate['scopes']) == 7
    assert set(scopes) == set(mapped_scopes) == set(EXPECTED_SCOPES)
    mapped_sources = {s['delivered_path']: s for s in mapping['reviewed_candidate_sources']}
    assert len(mapped_sources) == len(mapping['reviewed_candidate_sources']) == 33
    seen_sources, seen_names = set(), set()
    evidence_count = 0
    for scope_id, scope in scopes.items():
        source_count, declaration_count = EXPECTED_SCOPES[scope_id]
        assert len(scope['sources']) == source_count, scope_id
        assert len(scope['declarations']) == len(set(scope['declarations'])) == declaration_count
        assert not seen_names.intersection(scope['declarations']), scope_id
        seen_names.update(scope['declarations'])
        row = mapped_scopes[scope_id]
        assert (row['sources'], row['declarations']) == (source_count, declaration_count)
        for source in scope['sources']:
            path = source['path']
            assert path not in seen_sources, path
            seen_sources.add(path)
            expected = mapped_sources[path]
            assert expected['scope'] == scope_id
            assert expected['delivered_module'] == source['module']
            body = read(path)
            assert digest(body) == source['sha256'], path
            lines = body.decode().splitlines(keepends=True)
            changed = set()
            for replacement in source['import_normalizations']:
                index = replacement['line'] - 1
                assert 0 <= index < len(lines) and index not in changed
                changed.add(index)
                assert replacement['reviewed_line'] == 'import ' + replacement['from'] + '\n'
                assert replacement['delivered_line'] == 'import ' + replacement['to'] + '\n'
                assert lines[index] == replacement['delivered_line'], path
                lines[index] = replacement['reviewed_line']
            restored = digest(''.join(lines).encode())
            assert restored == source['reviewed_original_sha256'] == source['reviewed_sha256']
            assert restored == expected['reviewed_original_sha256'], path
            # source['reviewed_source'] is an archival label, never a read path.
        evidence = scope['review_evidence_hashes']
        assert set(scope['review_evidence']) == set(evidence), scope_id
        for path, wanted in evidence.items():
            assert digest(read(path)) == wanted, path
            evidence_count += 1
        for role in ('owner_validation', 'peer_validation'):
            path = scope[role]
            assert path in evidence, (scope_id, role)
            assert evidence[path] == row[role + '_sha256'], (scope_id, role)
            assert 'PASS' in read(path).decode(), path
    assert seen_sources == set(mapped_sources)
    assert seen_names == scoped_names

    inventory_rows = data('audit/declarations.json')
    inventory = {row['theorem']: row for row in inventory_rows}
    assert len(inventory_rows) == len(inventory)
    status = data('audit/STATUS.json')
    completed_status = status.get('status') == 'MODULE_M_AND_REPORT_SEMIALGEBRAIC_PATH_TARGETS_VERIFIED'
    require_central = args.require_central or completed_status or theorem_names <= set(inventory)
    if require_central:
        assert theorem_names <= set(inventory), 'Post-full validation requires all115 actual theorem declarations in the central inventory.'
    allowed_names = (set(inventory) | non_theorems) if require_central else set(inventory) | scoped_names
    for name in scoped_names.intersection(inventory):
        assert set(inventory[name]['axioms']) <= ALLOWED_AXIOMS, name

    spans, lines_total, exported = [], 0, set()
    assert len(snapshot['modules']) == 14
    for module in snapshot['modules']:
        source_bytes = permitted(repo, module['source']).read_bytes()
        assert digest(source_bytes) == module['source_sha256'], module['source']
        line_count = len(source_bytes.decode().splitlines())
        next_line = 1
        for span in module['coverage_spans']:
            assert span['start_line'] == next_line
            assert span['end_line'] >= next_line
            next_line = span['end_line'] + 1
            spans.append(span)
            exported.update(span.get('verified_exports', []))
        assert next_line == line_count + 1
        lines_total += line_count
    assert len(spans) == 172 and lines_total == 4323 and len(exported) == 2899
    # Existing historical references never need the pre-full152-name allowance.
    assert exported <= set(inventory), sorted(exported - set(inventory))
    assert mapping['existing_ACI_source_map'] == [m for m in snapshot['modules'] if m['module'] in ['A', 'C', 'I']]
    assert mapping['all_module_remaining_claims'] == [dict(module=m['module'], status=m['status'],
        remaining_claims=m.get('remaining_claims', [])) for m in snapshot['modules']]
    literal = mapping['literal_mapping']
    assert len(literal) == 8 and digest(canonical(literal)) == EXPECTED_LITERAL_ROWS
    assert {row['source'] for row in literal} == {'affine_geometry.tex', 'C.tex', 'inventory.tex'}
    for row in literal:
        assert set(row['declarations']) <= allowed_names, row['claim']
    assert mapping['component_relations_not_identified'] == ['ordinary_topological', 'ordinary_piecewise_smooth', 'continuous_semialgebraic']
    assert mapping['endpoint_derivatives_claimed'] is False
    assert mapping['subsequent_findings'] == [dict(source='foundation.tex', lines=[94, 99],
        finding='Exact Gram-sum identity not separately exported when discovered after this review.',
        status_at_discovery='separately_tracked_literal_mathematical_obligation')]
    assert mapping['subsequent_findings_are_historical_not_current_register'] is True
    assert mapping['remaining_exceptions'] == {'mathematical_source_attribution': 'R182-187 older unidentified four-piece objective',
        'documentary_evidence': 'E historical execution and archival records'}
    mode = 'all115 actual theorems required centrally;37 non-theorems scoped' if require_central else 'pre-full: only delivered aggregate115 theorems may augment current theorem inventory;37 non-theorems scoped'
    print(datetime.now(timezone.utc).isoformat())
    print('PASS:33 delivered sources reconstruct33 reviewed original hashes;7 frozen owner/peer PASS pairs;'
          f'{evidence_count} public evidence hashes;no excluded artifact reads.')
    print('PASS:fresh Lean declaration-kind report115 theorems/37 non-theorems;all152 actual scoped '
          'type/standard-axiom reports and16 exact contracts retained.')
    print('PASS:historical14-module/172-span/4323-line snapshot;2899 actual current references;'
          'eight exact A/C/I source rows;component/endpoint/history distinctions preserved.')
    print(f'PASS:{mode}. This is source/provenance validation, not a new Lean proof audit.')


if __name__ == '__main__':
    main()
