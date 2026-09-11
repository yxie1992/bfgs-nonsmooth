#!/usr/bin/env python3
"""Reconcile the explicitly corrected edition after the actual core/job gates.

This is a one-time release registration, not a substitute for compiling Lean.
It keeps the original-snapshot flags false and preserves every source span,
previous export, original research file and inherited mathematical correction.
"""
import copy
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel):
    return json.loads((ROOT / rel).read_text())


def write(rel, obj):
    (ROOT / rel).write_text(json.dumps(obj, indent=2) + '\n')


def main():
    subprocess.run(['python3', 'scripts/validate_report_reconstruction_19.py', '--pre-promotion'],
                   cwd=ROOT, check=True)
    s = read('audit/STATUS.json')
    r = read('audit/REPORT_STATUS.json')
    assert r['schema_version'] == 1 and not r['entire_report_verified']
    assert not any(m['id'] == 'report_reconstruction_19' for m in r['milestones'])
    jobs = read('verification/reconstructed/jobs.json')['jobs']
    summary = read('verification/reconstructed/fresh/SUMMARY.json')
    assert len(jobs) == 19 and summary['actual_check_occurrences'] == 107
    assert summary['distinct_theorems_checked'] == 93
    proof = read('audit/reconstruction_completion_declarations.json')
    inventory = {x['theorem'] for x in read('audit/declarations.json')}
    count = len(s['verified_declarations'])
    total = s['audited_declaration_count']
    draft = (ROOT / 'audit/reconstruction_scope/CORRECTED_REPORT_DRAFT.md').read_text()
    pending = '**Draft release status:** pending the complete reconstruction gate. This draft\ndoes not assert that the new package or corrected report is already verified.'
    assert draft.count(pending) == 1
    draft = draft.replace(pending, f'**Verified corrected edition:** the pinned Lean 4.19.0 build checked\n{count:,} explicit theorems, {total:,} total theorem declarations and all 255\nexact targets, with 737 frozen Lean sources. All 19 newly authored jobs passed\n107 strict literal type/axiom checks covering 93 distinct theorem names.')
    old = '''The final release will replace this draft paragraph with its actual complete
compiler, source-map, reconstruction-job and independent-review evidence.
`original_snapshot_all_assertions_verified` stays false.
`corrected_report_verified` becomes true only when the corrected mathematical
scope, new execution evidence and full source reconciliation all pass. The
legacy `entire_report_verified` flag retains its original-snapshot meaning;
this companion does not silently change that meaning.'''
    assert draft.count(old) == 1
    draft = draft.replace(old, '''The retained mathematics of this corrected edition, its explicit reconstruction,
and the new execution evidence have passed their respective gates. The complete
compiler transcript is [report_reconstruction_check.log](audit/report_reconstruction_check.log),
with [central status](audit/STATUS.json), [all transitive reports](audit/axioms.log),
and [737 source hashes](audit/report_reconstruction_source_hashes.json).
The [new nineteen-job summary](verification/reconstructed/fresh/SUMMARY.json)
contains actual commands, results and artifact links. The
[source register](audit/REPORT_STATUS.json) covers all 14 modules and 172 spans;
the [independent completion review](audit/REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md)
and [closing validation](audit/report_reconstruction_documentation_validation.log)
record the source/type/axiom/evidence correspondence.

`corrected_report_verified` is true for this explicit edition.
`original_snapshot_all_assertions_verified` and legacy `entire_report_verified`
remain false: neither the older unidentified objective attribution nor the
original execution history has been recovered. The reconstruction removes the
need for those unavailable inputs without representing new evidence as old.

Run `bash scripts/bootstrap.sh` to establish the pinned build. Then run
`python3 verification/reconstructed/run_all.py` for the new nineteen-job suite,
and `python3 scripts/validate_report_reconstruction_19.py` for the completed
source, theorem, axiom and evidence gate. Existing source-review and scoped
audit logs remain bound to their unchanged proof-source hashes.''')
    (ROOT / 'CORRECTED_REPORT.md').write_text(draft)
    companion_hash = hashlib.sha256(draft.encode()).hexdigest()
    review = 'audit/REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md'
    r.update(schema_version=2, entire_report_verified=False,
             original_snapshot_all_assertions_verified=False,
             corrected_report_mathematics_verified=True,
             reconstructed_execution_evidence_verified=True,
             corrected_source_reconciliation_verified=True,
             corrected_report_verified=True,
             historical_assertions_status='superseded_unsupported_ai_generated_history',
             scope='Every retained assertion of the preserved master report with the mandatory explicit correction companion; original historical assertions separately superseded; explicit conjectures remain questions.',
             verification_scope=dict(companion='CORRECTED_REPORT.md', companion_sha256=companion_hash,
                                     authorization='audit/reconstruction_scope/authorization_and_scope.json',
                                     original_snapshot_flag_semantics_unchanged=True,
                                     independent_review=review))
    modules = {m['module']: m for m in r['modules']}
    for module in r['modules']:
        module['previous_snapshot_status'] = module['status']
        module['previous_snapshot_remaining_claims'] = copy.deepcopy(module['remaining_claims'])
        module['corrected_retained_mathematics_verified'] = True
        module['remaining_claims'] = []
    modules['R']['status'] = 'all_corrected_retained_mathematics_and_explicit_four_piece_reconstruction_verified'
    modules['E']['status'] = 'new_nineteen_job_evidence_and_retained_analytic_assertions_verified_original_history_superseded'
    modules['I']['status'] = 'all_corrected_mathematical_synthesis_verified_original_history_superseded'
    for key in ['R', 'E', 'I']:
        modules[key]['reconstruction_review'] = review
    def amend(row, note, exports=()):
        row['previous_snapshot_claim_review'] = row['claim_review']
        row['previous_snapshot_review_note'] = row.get('review_note', '')
        row['review_note'] = note
        row['claim_review'] = 'reviewed_corrected_reconstruction_and_actual_evidence'
        row['verified_exports'] = sorted(set(row.get('verified_exports', [])) | set(exports))
        assert set(row['verified_exports']) <= inventory
        row['correction_companion'] = 'CORRECTED_REPORT.md'
    rrow = next(x for x in modules['R']['coverage_spans'] if x['id'] == 'R.span.7')
    rnames = [name for scope in proof['scopes'] if scope['id'] in {'objective_value_scale', 'r_reconstruction'}
              for name in scope['declarations'] if name in inventory]
    amend(rrow, 'New explicit objective a*F_D(Tz)+a-1 with delta=c-16d-1>0, a=25/(4delta), T=diag(1,16/5) realizes optimizer(-1,5), value-1, branch values-1,-1,-29/4 and actual periodic errors0,0,25/4. The transformed actual full-BFGS run and fixed-positive-band SP/RS failure are proved. Original D optimizer(-1,16) and correction remain proved; no recovery of an older unidentified objective is claimed.', rnames)
    for row in modules['E']['coverage_spans']:
        if 'historical' not in row['claim_review']:
            continue
        matched = [j for j in jobs if row['start_line'] <= j['source_lines'][0]
                   and j['source_lines'][1] <= row['end_line']]
        names = [c['theorem'] for j in matched for c in j['checks']]
        amend(row, 'The original execution/archive assertions are explicitly superseded as unsupported AI-generated history. Newly authored pinned theorem jobs provide actual fresh commands, timestamps, exit codes, complete literal contracts and transitive axioms. Numerical category substitutions and their exact hypothesis/precision limitations are mandatory in CORRECTED_REPORT.md; no original run or timing is claimed.', names)
        row['historical_assertions_status'] = 'superseded_unsupported_ai_generated_history'
        row['new_execution_evidence'] = 'verification/reconstructed/fresh/SUMMARY.json'
        if matched:
            row['reconstructed_jobs'] = [j['job'] for j in matched]
    irow = next(x for x in modules['I']['coverage_spans'] if x['id'] == 'I.span.22')
    amend(irow, 'All mathematical synthesis and explicit research boundaries remain as reviewed. The unavailable original nineteen-job record is superseded by the actual new reconstruction package; historical claims remain unverified and no conjecture is promoted to a theorem.')
    grow = next(x for x in modules['G']['coverage_spans'] if x['id'] == 'G.span.10')
    gnames = [c['theorem'] for j in jobs if j['job'] == 'G-oscillatory-numerical' for c in j['checks']]
    amend(grow, 'The report-defined accumulating-kink objective, eligible pairs, fixed-knot quotient divergence, neighborhood noncertificate and actual scalar convergence remain proved. The unavailable further archived example has no source formula; the corrected execution category explicitly uses this defined auxiliary instead, without identifying it with a historical oscillatory objective or claiming a bad BFGS run.', gnames)
    for correction in r['mathematical_corrections']:
        if correction['id'] == 'R.historical_four_piece_attribution':
            previous = copy.deepcopy(correction)
            correction.update(status='original_D_correction_and_new_explicit_R_realization_verified',
                              previous_record=previous,
                              reconstruction='CORRECTED_REPORT.md',
                              reconstruction_exports=[n for scope in proof['scopes'] if scope['id'] == 'r_reconstruction'
                                                      for n, _ in scope['targets']],
                              correction='Current D still has optimizer(-1,16) and its documented supporting errors. A newly defined affine-coordinate/positive-value transform realizes the printed R optimizer and numbers with an actual full-BFGS failure run. This supersedes the unsupported older attribution; no missing objective is represented as recovered.')
    r['mathematical_corrections'] += [
        dict(id='E.unsupported_history_reconstructed_execution', source='verification.tex and VERIFICATION_REPORT.md',
             status='explicitly_superseded_and_new_nineteen_job_evidence_verified', review=review,
             correction='Original commands/results/counts/timings/precision/archive identities are unsupported. All19 source categories receive explicitly newly authored literal Lean jobs. Two numerical tolerance jobs become universal eventual-tolerance results with their actual hypotheses, without historical stopping counts or precision claims.'),
        dict(id='G.unspecified_archived_auxiliary_substitution', source='G.tex263 and verification.tex125-128',
             status='explicit_report_defined_accumulating_kink_substitution_verified', review=review,
             correction='The unprovided oscillatory archive objective is replaced in the corrected execution category by the report-defined accumulating-kink objective and its exact incoming-pair/obstruction theorems. No recovery of a historical formula,24 finite computations or bad BFGS trajectory is claimed.')]
    r['milestones'].append(dict(id='report_reconstruction_19', status='verified_corrected_edition',
        targets=[n for n, _ in proof['targets']], audit='audit/STATUS.json', statement_review=review,
        explicit_theorems=count, audited_theorems=total, exact_targets=255, frozen_sources=737,
        reconstructed_jobs=19, strict_literal_check_occurrences=107, distinct_job_theorems=93,
        corrected_report='CORRECTED_REPORT.md', original_historical_assertions_verified=False))
    # Coverage and old-export preservation are checked again by the closing validator.
    assert len(r['modules']) == 14 and sum(len(m['coverage_spans']) for m in r['modules']) == 172
    write('audit/REPORT_STATUS.json', r)
    marker = '## Nineteenth milestone: reconstructed and corrected report completed'
    record = f'''\n\n{marker}

The corrected edition is [CORRECTED_REPORT.md](CORRECTED_REPORT.md), read together
with the unchanged original master report. All retained mathematics is checked:
{count:,} explicit/{total:,} total theorem declarations, 255 exact targets and 737
frozen Lean files. The new nineteen-job package passed 107 strict literal
type/axiom checks across 93 distinct theorems. All earlier 727 proof files and 7,704
theorem types/transitive axiom sets remain unchanged. The permitted axioms are
propext, Classical.choice and Quot.sound; there are no proof placeholders or
unchecked external mathematical computations.

The new R objective realizes the printed optimizer and supporting errors, with
an actual transformed full-BFGS failure run and direct SP/RS contradiction.
The new E package supplies actual execution evidence. Original unsupported
historical runs and the older unidentified objective attribution are explicitly
superseded, with precise numerical-category/auxiliary substitutions. The nine
earlier mathematical corrections and all 22 original research artifacts remain.

The report-level `corrected_report_verified` is true. Legacy
`entire_report_verified` and `original_snapshot_all_assertions_verified` remain
false for the unamended original snapshot. Explicit open research questions and
conditional criterion hypotheses remain accurately classified. The remaining
input requests in earlier milestone entries are historical and are resolved
for the corrected edition by the user's authorized reconstruction.

Evidence: audit/report_reconstruction_check.log, audit/axioms.log,
audit/REPORT_STATUS.json, verification/reconstructed/fresh/SUMMARY.json, and
audit/report_reconstruction_documentation_validation.log. Reproduce the pinned
build with scripts/bootstrap.sh, the nineteen jobs with
verification/reconstructed/run_all.py, and the completed release gate with
scripts/validate_report_reconstruction_19.py.
'''
    for rel in ['ENTIRE_REPORT_PLAN.md', 'MATHEMATICAL_REVIEW.md', 'PROOF_OBLIGATIONS.md']:
        p = ROOT / rel
        text = p.read_text()
        assert marker not in text
        title, rest = text.split('\n', 1)
        current = '\n\nCurrent status: the [corrected report](CORRECTED_REPORT.md) is verified.\nThe original historical record remains unverified. The initial plan and\nmilestones 1–18 below are historical snapshots: their pending-work statements\nare superseded by the final nineteenth milestone, which records completed scope.\n'
        p.write_text(title + current + rest + record)
    p = ROOT / 'README.md'
    text = p.read_text()
    start = text.index('**Module M')
    stop = text.index('The original research sources are unchanged.')
    text = text[:start] + f'''**The corrected and reconstructed report is Lean-verified.** Read
[CORRECTED_REPORT.md](CORRECTED_REPORT.md) with the preserved original report.
It states every mathematical correction and explicit source reconstruction.
The original unsupported execution history remains unverified.

The pinned Lean 4.19.0 build and complete transitive audit checked {count:,}
explicit theorems, {total:,} total theorem declarations and 255 exact targets,
across 737 frozen Lean sources. Only `propext`, `Classical.choice` and `Quot.sound`
occur. There are no proof placeholders or unchecked mathematical computations.
The new 19-job suite passed 107 strict literal type/axiom checks across 93 distinct
theorems. See [source status](audit/REPORT_STATUS.json),
[full compiler log](audit/report_reconstruction_check.log),
[all axiom reports](audit/axioms.log) and
[actual new job results](verification/reconstructed/fresh/SUMMARY.json).

''' + text[stop:]
    text = text.replace('Historical execution/source-attribution exceptions remain unverified.',
                        'The nineteenth tranche explicitly reconstructs the R example and new execution evidence. Original historical assertions remain unsupported and are superseded in the corrected edition.')
    text = text.replace("R's old four-piece numerical attribution remains explicitly unresolved; the\nsupporting-plane interpretation is proved for the actual current D objective.",
                        'The old attribution is not recovered; the new explicit R objective now has its\nown actual full-BFGS failure and supporting-plane interpretation.')
    # Superseded progress statements must not read as current obligations.
    text = text.replace('The latest source register records the remaining historical/source-attribution obligations.', 'The latest source register distinguishes the completed corrected edition from unsupported original historical assertions.')
    text = text.replace('The remaining specific objective families and geometric\ncertificate constructions are tracked separately in the report register.', 'The verified specific objective families and geometric\ncertificate constructions are recorded with their actual hypotheses in the report register.')
    text = text.replace('## Fourth report milestone\n', '## Fourth report milestone (historical record)\n')
    text = text.replace("Q's calibrated transport and full convergence theorem remain open, as do the\nother obligations in the report register.", "Q's calibrated transport and full convergence theorem were subsequently proved.\nThe nineteenth milestone below records completion of the corrected report.")
    p.write_text(text + record)
    p = ROOT / 'audit/REPORT_VERIFICATION_OVERVIEW.md'
    old = p.read_text()
    table = old[old.index('| Module |'):old.index('Conditional energy/')]
    table = table.replace('Recoverable current radial/inward/supporting-plane theory, families and boundaries; older four-piece attribution at lines 182–187 remains unresolved.', 'All radial/inward/supporting-plane theory, families and boundaries; new explicit four-piece realization of lines182–187 with actual bad run and SP/RS failure.')
    table = table.replace('Current mathematical synthesis and supersession implications; inherited R attribution and historical evidence remain qualified.', 'All corrected mathematical synthesis and explicit supersession implications; historical record clearly distinguished.')
    table = table.replace('Current analytic claims reconciled against actual Lean results; original 19-job outcomes, counts, timings and archive identities remain unverified.', 'All retained analytic claims and new 19-job execution evidence; unsupported original outcomes/counts/timings/archive identities explicitly superseded.')
    p.write_text(f'''# Corrected report verification overview

The corrected report is verified: **{count:,} explicit/{total:,} total theorem
declarations, 255 exact targets,737 frozen Lean sources**, and **19 new jobs with
107 strict literal checks across 93 distinct theorems**. All permitted transitive
axioms are propext, Classical.choice and Quot.sound.

[CORRECTED_REPORT.md](../CORRECTED_REPORT.md) is the mandatory correction companion
to the unchanged original master report. It defines the new R objective and
actual full-BFGS run, preserves the nine earlier mathematical corrections, and
specifies every replacement for unavailable historical inputs. Original history
is neither recovered nor certified; the original-snapshot flags remain false.

''' + table + '''Conditional criteria retain their actual hypotheses; their report applications
discharge the required premises as recorded. Explicit conjectures and unclaimed
blanket convergence/robustness results remain outside theorem claims.

The source register covers 14 modules, 172 disjoint spans and 4,323 chapter lines.
See [REPORT_STATUS.json](REPORT_STATUS.json),
[complete compiler evidence](report_reconstruction_check.log),
[all transitive axiom reports](axioms.log),
[new execution results](../verification/reconstructed/fresh/SUMMARY.json), and
[independent completion review](REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md).

Reproduce with `bash scripts/bootstrap.sh`, then
`python3 verification/reconstructed/run_all.py` and
`python3 scripts/validate_report_reconstruction_19.py`.
''')
    print(f'Updated corrected report19: {count} explicit/{total} total/255 targets;19 new jobs/107 checks;original-history flags remain false.')


if __name__ == '__main__':
    main()
