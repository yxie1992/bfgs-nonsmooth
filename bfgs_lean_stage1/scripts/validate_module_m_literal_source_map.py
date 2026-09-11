#!/usr/bin/env python3
"""Validate the literal Module M map against actual source, kinds and central audit.

Read-only and delivered-only. This checks existing compiler evidence; it does
not supply a mathematical proof or treat a historical scope as the full gate.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path, PurePosixPath

MAP_HASH = '55c0435d35b1e6c4f18820ebbcb36cb22047591851ecb7ba4a39cebb73de3da9'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def safe(root, relative):
    rel = PurePosixPath(relative)
    assert not rel.is_absolute() and '..' not in rel.parts, relative
    assert rel.parts[:2] != ('audit', 'scratch'), relative
    path = root.joinpath(*rel.parts)
    resolved = path.resolve()
    assert resolved.is_relative_to(root.resolve()), relative
    assert resolved.relative_to(root.resolve()).parts[:2] != ('audit', 'scratch'), relative
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--repository-root', type=Path)
    args = parser.parse_args()
    root = args.project_root.resolve()
    repo = (args.repository_root or root.parent).resolve()
    read = lambda rel: safe(root, rel).read_bytes()
    data = lambda rel: json.loads(read(rel))
    raw = read('audit/module_m_literal_source_map.json')
    assert hashlib.sha256(raw).hexdigest() == MAP_HASH
    mapping = json.loads(raw)
    source = safe(repo, mapping['source']).read_bytes()
    assert hashlib.sha256(source).hexdigest() == mapping['source_sha256']
    assert len(source.decode().splitlines()) == mapping['line_count'] == 248
    assert len(mapping['spans']) == 5
    assert [span['id'] for span in mapping['spans']] == [f'M.span.{i}' for i in range(1, 6)]
    assert [i for span in mapping['spans']
            for i in range(span['start_line'], span['end_line'] + 1)] == list(range(1, 249))
    names = {name for span in mapping['spans'] for name in span['declarations']}
    assert len(names) == 53
    assert mapping['original_source_edited'] is False
    manifest = data('audit/module_m_literal_completion_declarations.json')
    assert set(mapping['supplemental_targets']) == {name for name, _ in manifest['targets']}

    hashes = data('audit/module_m_literal_source_kinds_hashes.json')
    assert set(hashes) == {'audit/ModuleMLiteralSourceKinds.lean',
                          'audit/module_m_literal_source_kinds.log',
                          'audit/module_m_literal_source_map.json'}
    for rel, digest in hashes.items():
        assert hashlib.sha256(read(rel)).hexdigest() == digest, rel
    log = read('audit/module_m_literal_source_kinds.log').decode()
    assert 'error:' not in log
    kinds = re.findall(r'^M_SOURCE_KIND (\S+) (\S+)$', log, re.M)
    assert len(kinds) == len(dict(kinds)) == 53
    assert set(dict(kinds)) == names
    # Every mapped constant was queried in Lean. No name-based kind exemption.
    assert {kind for _, kind in kinds} == {'theorem'}
    ax = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(ax) == 1 and ax[0][0] == 'BfgsVerification.hessianUpdate'
    assert set(ax[0][1].replace(',', ' ').split()) <= ALLOWED

    rows = data('audit/declarations.json')
    inventory = {row['theorem']: row for row in rows}
    assert len(rows) == len(inventory)
    status = data('audit/STATUS.json')
    assert status['status'] == 'MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
    assert not status['unexpected_axioms'] and not status['missing_axiom_reports']
    assert not status['remaining_target_obligations']
    assert len(inventory) == status['audited_declaration_count']
    assert names <= set(inventory), sorted(names - set(inventory))
    for name in names:
        assert set(inventory[name]['axioms']) <= ALLOWED, name
    for name, signature in manifest['targets']:
        assert inventory[name]['signature'] == signature, name
    print(datetime.now(timezone.utc).isoformat())
    print('PASS: unchanged foundation source; all 248 lines in five disjoint spans; '
          '53 actual queried theorem kinds and all 53 complete central axiom reports.')
    print('PASS: both supplemental exact targets are central; ordinary hessianUpdate '
          'axioms checked; no definition exemption or excluded scratch input.')


if __name__ == '__main__':
    main()
