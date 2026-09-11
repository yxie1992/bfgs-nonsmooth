#!/usr/bin/env python3
"""Promote literal path coverage only after the frozen seventeenth full gate."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
s = json.loads((ROOT / 'audit/STATUS.json').read_text())
assert s['status'] == 'MODULE_M_AND_REPORT_SEMIALGEBRAIC_PATH_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
assert not s['remaining_target_obligations']
hashes = json.loads((ROOT / 'audit/report_semialgebraic_path_source_hashes.json').read_text())
assert len(hashes) == 726
for f, h in hashes.items():
    assert hashlib.sha256((ROOT / f).read_bytes()).hexdigest() == h, f
manifest = json.loads((ROOT / 'audit/semialgebraic_path_completion_declarations.json').read_text())
assert len(manifest['declarations']) == 152 and len(manifest['targets']) == 16
p = ROOT / 'audit/REPORT_STATUS.json'
r = json.loads(p.read_text())
assert not any(m['id'] == 'report_semialgebraic_path_17' for m in r['milestones'])
mods = {m['module']: m for m in r['modules']}
review = 'audit/REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md'


def exports(files):
    result = []
    for f in files:
        found = [d['theorem'] for d in s['verified_declarations']
                 if d['source'].endswith('/' + f + '.lean')]
        assert found, f
        result += found
    return sorted(set(result))


def span(tag, i, files, note):
    row = next(x for x in mods[tag]['coverage_spans'] if x['id'] == f'{tag}.span.{i}')
    row.update(claim_review='reviewed_all_retained_literal_mathematical_claims_audited',
               review_note=note)
    row.pop('verification_note', None)
    row['verified_exports'] = sorted(set(row.get('verified_exports', []) + exports(files)))


mods['M'].update(status='principal_targets_verified_literal_sum_identity_and_sharp_potential_degree_pending',
                 remaining_claims=[
                     'Foundation94–99 literal augmented-Gram/eigenvalue double-sum equality; the proved matrix hierarchy used a direct inequality proof.',
                     'Foundation151 sharp degree at most n−1 of the optimized finite potential; the proved superquadratic theorem used a sufficient degree-n bound.'])
for i in [2, 3]:
    row = next(x for x in mods['M']['coverage_spans'] if x['id'] == f'M.span.{i}')
    row['claim_review'] = 'principal_conclusions_audited_additional_literal_proof_identity_tracked'
    row['review_note'] = mods['M']['remaining_claims'][i - 2]

mods['A'].update(status='all_retained_mathematical_claims_and_literal_geometric_ingredients_verified',
                 statement_review=review, remaining_claims=[])
span('A', 4, ['SemialgebraicPathCover', 'SemialgebraicPathCoverTargets',
             'ContinuousSemialgebraicComponents', 'AffineCriticalSemialgebraicPathComponents',
             'SemialgebraicScalarSmooth', 'ObjectiveSemialgebraicComposition',
             'ObjectiveSemialgebraicCompositionTargets', 'CriticalSmoothPathValues'],
     'Actual semialgebraic graphs, finite path covers, arbitrary continuous-semialgebraic '
     'path classes and their same-curve finite-smoothness upgrade are proved. Actual F-composition '
     'is continuous on the closed interval and smooth off a finite interior exceptional set. '
     'The actual affine-critical classes are finite, semialgebraic, internally path connected '
     'and constant in F. Projection, decomposition, finite values and derivative regularity '
     'are derived, not premises. Earlier ordinary-component, finite-value and original low-gap '
     'conclusions remain proved. No endpoint derivative assertion is added.')
mods['C'].update(status='all_retained_mathematical_claims_verified_with_documented_C2_to_C1_qualification',
                 statement_review=review, remaining_claims=[])
span('C', 12, ['CriticalSmoothPathValues', 'CriticalSmoothPathTargets',
              'ObjectiveSemialgebraicCompositionTargets', 'ContinuousSemialgebraicComponents'],
     'Actual finite critical values, ordinary/smooth/continuous-semialgebraic path class facts '
     'and constant objective values are proved, with the literal composition regularity '
     'ingredient. The original planar low/local basins retain an objective-only threshold '
     'before every run, strict contours and local regularity. No optimal multiplier, '
     'decomposition, finite-value or convergence hypothesis is introduced. The documented '
     'C2-to-C1 constant-rank qualification and expressly open rotating-normal case remain.')
mods['I']['remaining_claims'] = (
    'Historical execution/archive assertions and the unidentified older R numerical attribution '
    'remain unresolved. All current mathematical synthesis, including the literal A path '
    'ingredients, ordinary-component/finite-critical-value/low-gap assertions and C basins, '
    'is proved. The older numerical claim is not silently retired.')
span('I', 21, ['AffineCriticalSemialgebraicPathComponents', 'CriticalSmoothPathValues'],
     'All actual geometric synthesis claims are proved: ordinary components, actual '
     'continuous-semialgebraic and smooth path classes, constant critical values, finite '
     'critical-value image and original low gap. The literal path and composition ingredients '
     'are now also audited. Equal-rate, compact-gap and incoming-jump claims remain proved; '
     'no blanket BFGS claim follows.')
mods['E']['remaining_claims'] = (
    'Historical 19-job outcomes, exact counts/timings/environment and original script/archive '
    'identities lack the referenced inputs and remain unverified. Current actual mathematical '
    'proofs include general elimination, literal semialgebraic paths and composition, finite '
    'critical values, low gaps and C basins. The unidentified older R numerical objective '
    'remains a separate mathematical source-attribution obligation.')
row = next(x for x in mods['E']['coverage_spans'] if x['id'] == 'E.span.24')
row['review_note'] = (
    'Current compiled proofs supersede historical draft status for corresponding declarations, '
    'including general elimination and all literal A path/composition/critical-value/low-gap '
    'ingredients and C basins. They do not certify the specific past execution records. '
    'Rotating normals, positive-measure/floating-point robustness, rounded stable-manifold '
    'points and blanket convergence remain expressly unclaimed.')
e = len(s['verified_declarations'])
a = s['audited_declaration_count']
r['milestones'].append(dict(
    id='report_semialgebraic_path_17', status='verified',
    targets=[b for _, b in manifest['targets']], audit='audit/STATUS.json',
    statement_review=review, explicit_theorems=e, audited_theorems=a, exact_targets=249,
    conditional_infrastructure=[
        'Reusable cover/value/regularity implications retain explicit hypotheses; actual '
        'semialgebraic applications discharge those hypotheses.',
        'The unidentified older R numerical objective remains an unresolved mathematical attribution.',
        'Historical execution records and archive identities remain unverified.',
        'M literal Gram-sum identity and sharp degree-n−1 potential bound remain under separate verification.']))
r['entire_report_verified'] = False
p.write_text(json.dumps(r, indent=2) + '\n')

marker = '## Seventeenth milestone: literal semialgebraic paths and composition'
text = f'''\n\n{marker}

The pinned full build and transitive audit passed {e:,} explicit theorems,
{a:,} total theorem declarations, 249 exact targets and 726 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual closed evidence is
in report_semialgebraic_path_check.log, STATUS.json and the source/hash records.

Actual semialgebraic path graphs, a finite cover in arbitrary dimension,
finite actual continuous-semialgebraic path classes, same-curve regularity and
actual objective composition now close A's literal geometric proof ingredients.
Continuity includes the closed interval; smoothness is asserted off a finite
set of interior parameters, without endpoint derivative claims. C's literal
smooth-path constancy and I's synthesis are covered. All earlier mathematical
corrections remain explicit and the original research sources are unchanged.

M's principal theorems remain verified. The source's additional exact Gram-sum
identity and sharp degree-n−1 potential bound were found to need explicit
exports beyond the sufficient inequalities used in those proofs. They remain
a separate active scope until their delivered compiler/audit gate passes.

R182–187's older four-piece objective is unidentified, so its printed numerical
attribution remains a mathematical obligation. E's original 19-job archive,
counts, timings and execution identities remain unverified. Current D's proved
correction and current universal Lean proofs do not establish those missing
source facts. The entire original report flag remains false pending resolution;
no claim has been silently dropped or replaced by an added assumption.
'''
for name in ['ENTIRE_REPORT_PLAN.md', 'MATHEMATICAL_REVIEW.md', 'PROOF_OBLIGATIONS.md']:
    p = ROOT / name
    old = p.read_text()
    assert marker not in old
    p.write_text(old + text)
p = ROOT / 'README.md'
old = p.read_text().replace(
    'all 5,002 explicit\ntheorems and 7,486 theorem declarations including generated auxiliaries. All 233',
    f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 249')
old = old.replace('audit/report_tame_geometry_check.log', 'audit/report_semialgebraic_path_check.log', 1)
old = old.replace(
    "A's stronger literal semialgebraic-path/general-composition ingredient remains\nactive; historical execution/source-attribution exceptions remain unverified.",
    "The seventeenth tranche proves A's literal semialgebraic path graphs, actual\n"
    'path classes and general objective-composition regularity. See\n'
    '[audit/REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md](audit/REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md).\n'
    'Historical execution/source-attribution exceptions remain unverified.')
old = old.replace('remaining literal A path/composition\nand historical/source-attribution obligations.',
                  'remaining historical/source-attribution obligations.')
old = old.replace('After the audit output log has closed and intended delivery files have been',
                  'The checker allows up to 7,200 seconds per build or audit command. The\n'
                  'complete inventory takes substantially longer than the former ten-minute\n'
                  'default; use `--timeout SECONDS` to change the limit.\n\n'
                  'After the audit output log has closed and intended delivery files have been')
p.write_text(old)
p = ROOT / 'audit/I_SOURCE_RECONCILIATION.md'
old = p.read_text().replace('stronger literal path-graph facts in A remain separately tracked.',
                           'the stronger literal path-graph and objective-composition facts in A are now also proved.')
p.write_text(old)
p = ROOT / 'audit/HISTORICAL_EVIDENCE_RECONCILIATION.md'
old = p.read_text().replace(
    'The stronger literal A semialgebraic-path-graph/general composition ingredient remains separately active.',
    'The stronger literal A semialgebraic path graphs, actual continuous-semialgebraic path '
    'classes and general objective-composition regularity are also proved.')
p.write_text(old)
overview = f'''# Report verification overview

The seventeenth complete pinned Lean build and transitive axiom audit passed:
**{e:,} explicit theorems, {a:,} total theorem declarations, 249 exact targets,
726 frozen Lean files**. Only propext, Classical.choice and Quot.sound occur.
No sorry/admit, custom mathematical axioms or unchecked mathematical computation
is used. Every original research source is preserved.

The entire original report is **not yet verified**: the older R numerical
attribution lacks its defining objective, and E's historical execution archive
is absent. M's additional literal Gram-sum identity and sharp potential-degree
export are also in a separate active scope; its principal theorem chain is proved.

| Module | Verified scope / remaining item |
|---|---|
| M | Actual full-BFGS principal determinants and matrix hierarchy, derived normalized hierarchy, reciprocal means, finite horizon and superquadratic growth; actual objective-run bridges. Literal Gram-sum equality and sharp potential degree remain separately active. |
| T | Transported-certificate convergence and stated variants, with explicit certificate hypotheses. |
| R | Recoverable current radial/inward/supporting-plane theory, families and boundaries; older four-piece attribution at lines 182–187 remains unresolved. |
| F | Stated structural families, local basins, affine lifting and rates, with documented proof replacements. |
| H | Homogeneous value dichotomy, recurrent affine geometry, stated low-rank convergence and examples; explicit higher-rank questions remain questions. |
| Q | Actual parabolic envelope, ordered pruning, printed certificate field, convergence and radial separation. |
| G | Scalar convergence, certificate geometry and nonnecessity, with the documented accessible/all-active-span correction. |
| A | Actual affine-critical geometry, general semialgebraic projection, literal paths/composition/components, finite critical values and original low gap. |
| C | Stated planar convergence/basins and proof ingredients, with the documented C2-to-C1 regularity qualification. |
| U | Stated fixed-normal/parallel-interface results and examples, with the nonzero-jump qualification. |
| D | Actual exact seed, all deterministic search decisions, infinite failure and embeddings; five displayed rounding corrections documented. |
| L | Actual return-map dynamics, stable-orbit construction, infinite failure, regularity and embeddings; Jacobian rounding correction documented. |
| I | Current mathematical synthesis and supersession implications; inherited R attribution and historical evidence remain qualified. |
| E | Current analytic claims reconciled against actual Lean results; original 19-job outcomes, counts, timings and archive identities remain unverified. |

Conditional energy/frame/cover/value helpers remain identified in STATUS.json.
Their hypotheses are retained as criterion hypotheses or discharged by their
actual objective applications as documented. The source's explicit conjectures
and expressly unclaimed blanket BFGS/robustness conclusions are not theorem
completion targets.

The source register covers all 14 modules, 172 disjoint spans and 4,323 chapter
lines. See [REPORT_STATUS.json](REPORT_STATUS.json) for exact exports and source
hashes, [the statement review](REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md) for
the final geometric hypotheses and definitions, and
[STATUS.json](STATUS.json), [the complete checker transcript](report_semialgebraic_path_check.log)
and [axioms.log](axioms.log) for actual compiler and dependency evidence.

The remaining Lean work is M's literal Gram-sum identity and sharp potential
degree export. To finish the unresolved original-source claims, recover the older four-piece
objective used in R182–187 and the verification archive identified by E. The
current D objective and newly executed Lean proofs do not identify those
missing inputs. Any correction or retirement must be explicit and preserve
the original record.

Reproduce with the pinned toolchain using `bash scripts/bootstrap.sh`, or run
`python3 scripts/check.py` once dependencies are available. The default command
timeout is 7,200 seconds. Stage intended delivery files only after logs close,
regenerate MANIFEST.json, review the source/status correspondence, then commit
and push the completed milestone.
'''
(ROOT / 'audit/REPORT_VERIFICATION_OVERVIEW.md').write_text(overview)
print(f'Seventeenth register/docs updated: {e} explicit/{a} total/249 exact targets; '
      'M literal supplemental exports and historical/source-attribution claims remain; entire_report_verified=false.')
