#!/usr/bin/env python3
"""One-time, prose-only qualification of the core-versus-report status label.

Run after the first successful nineteenth core audit and before its final rerun.
The prior transcript and exact checker/registration hashes are retained. This
changes no proof source, target, compilation criterion or axiom criterion.
"""
import datetime
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    status = json.loads((ROOT / 'audit/STATUS.json').read_text())
    assert status['status'] == 'MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED'
    assert status['explicit_theorem_declarations'] == 5195 and status['audited_declaration_count'] == 7813
    assert not status['unexpected_axioms'] and not status['remaining_target_obligations']
    validation = ROOT / 'audit/report_reconstruction_initial_core_validation.log'
    assert 'PASS: 5195 explicit/7813 total theorems;255 exact targets;737 source hashes' in validation.read_text()
    rp = ROOT / 'audit/reconstruction_completion_registration.json'
    registration = json.loads(rp.read_text())
    checker = ROOT / 'scripts/check.py'
    assert sha(checker) == registration['check_sha256']
    before = 'The entire report remains incomplete. '
    after = 'Original-snapshot historical assertions remain unverified; corrected-report completion is recorded separately in REPORT_STATUS.json. '
    text = checker.read_text()
    assert text.count(before) == 1 and after not in text
    updated = text.replace(before, after, 1)
    record = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  before=before, after=after,
                  checker_before_sha256=sha(checker),
                  checker_after_sha256=hashlib.sha256(updated.encode()).hexdigest(),
                  registration_before=registration,
                  proof_source_freeze_sha256=sha(ROOT / 'audit/report_reconstruction_source_hashes.json'),
                  first_full_check_sha256=sha(ROOT / 'audit/report_reconstruction_check.log'),
                  first_core_validation_sha256=sha(validation),
                  proof_or_criterion_change=False,
                  final_full_rerun_required=True)
    out = ROOT / 'audit/reconstruction_status_wording_amendment.json'
    oldlog = ROOT / 'audit/report_reconstruction_initial_check.log'
    assert not out.exists() and not oldlog.exists()
    (ROOT / 'audit/report_reconstruction_check.log').rename(oldlog)
    checker.write_text(updated)
    registration = dict(registration, check_sha256=record['checker_after_sha256'],
                        status_wording_amendment='audit/reconstruction_status_wording_amendment.json')
    rp.write_text(json.dumps(registration, indent=2) + '\n')
    out.write_text(json.dumps(record, indent=2) + '\n')
    print('Qualified one status sentence; first successful transcript preserved; all proof sources, targets and checking criteria unchanged. Final full rerun required.')


if __name__ == '__main__':
    main()
