#!/usr/bin/env python3
"""Publish milestone15 documentation only after the frozen full audit passes."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
s = json.loads((ROOT / 'audit/STATUS.json').read_text())
assert s['status'] == 'MODULE_M_AND_REPORT_ALGEBRA_COMPLETION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
assert not s['remaining_target_obligations']
hashes = json.loads((ROOT / 'audit/report_algebra_completion_source_hashes.json').read_text())
assert len(hashes) == 633
for f, h in hashes.items():
    assert hashlib.sha256((ROOT / f).read_bytes()).hexdigest() == h, f
p = ROOT / 'audit/REPORT_STATUS.json'
r = json.loads(p.read_text())
assert not any(m['id'] == 'report_algebra_completion_15' for m in r['milestones'])
mods = {m['module']: m for m in r['modules']}
review = 'audit/REPORT_ALGEBRA_COMPLETION_STATEMENT_REVIEW.md'


def exports(files):
    out = []
    for f in files:
        found = [d['theorem'] for d in s['verified_declarations']
                 if d['source'].endswith('/' + f + '.lean')]
        assert found, f
        out += found
    return sorted(set(out))


def span(tag, i, state, files, note):
    row = next(x for x in mods[tag]['coverage_spans'] if x['id'] == f'{tag}.span.{i}')
    row.update(claim_review=state, review_note=note)
    row.pop('verification_note', None)
    if files:
        row['verified_exports'] = sorted(set(row.get('verified_exports', []) + exports(files)))


mods['A'].update(
    status='general_semialgebraic_projection_and_actual_critical_definability_verified_finite_path_value_closure_pending',
    statement_review=review + '; audit/GENERAL_PROJECTION_STATEMENT_REVIEW.md; audit/AFFINE_CRITICAL_DEFINABILITY_STATEMENT_REVIEW.md',
    remaining_claims='Finite semialgebraic smooth path/component decomposition, actual finite affine-critical values and low-level gap. Actual arbitrary-degree Boolean/finite-coordinate projection and actual supporting/critical-set/critical-graph definability are now proved; the conditional finite-path-cover implication does not discharge the remaining premise.')
span('A', 4, 'reviewed_general_projection_and_actual_critical_definability_audited_finite_path_value_closure_pending',
     ['GeneralProjectionTargets', 'AffineCriticalDefinability'],
     'Actual root-index recursion, simultaneous sign determination and finite sampling derive arbitrary finite-coordinate Boolean projection. Actual signed bounded support witnesses derive actual critical set/graph definability, including dimension zero. Finite smooth paths, components, values and the low gap remain explicit obligations.')
mods['H'].update(status='all_retained_mathematical_claims_verified', remaining_claims=[],
                 statement_review=review + '; audit/H_SHARP_CARDINALITY_INDEPENDENT_PEER_REVIEW.md; audit/TWO_PIECE_TERMINATION_STATEMENT_REVIEW.md')
for i in [5, 14]:
    span('H', i, 'reviewed_internal_claims_and_actual_cardinality_two_piece_cross_references_audited',
         ['SeedRecurrentRank', 'TwoPieceTargets'],
         'Actual seed recurrent set has three distinct slopes, span rank two and cardinality=rank+1, for every original permitted constant pair; actual positive values and iterates tend to a nonstationary zero. Attributed two-piece termination was audited in milestone14. No many-piece finite-termination or higher-rank zero-value iterate theorem is inferred.')
mods['D'].update(
    status='actual_construction_precision_original_box_denominators_and_Euclidean_locality_verified_literal_wrappers_pending',
    statement_review=review + '; audit/D_SOURCE_MAP.md; audit/D_SOURCE_SUPPLEMENT_STATEMENT_REVIEW.md',
    remaining_claims='Four source-map groups await literal exports for the non-strict interpreter, original-box polynomial iff, zero exclusion from the three-gradient convex hull and exact positive affine weights. Main construction, all actual strict queries, numerical precision, whole-box actual update denominators and literal Euclidean nine-query bound are audited. Historical package execution remains distinct.')
for i in [3, 5, 7]:
    row = next(x for x in mods['D']['coverage_spans'] if x['id'] == f'D.span.{i}')
    span('D', i, row['claim_review'] + '_and_actual_decimal_precision', ['DDisplayPrecision'],
         'The original mathematical construction remains verified. Actual displayed values are enclosed to one decimal unit, with five nearest-rounding corrections documented; no rounded number replaces the exact algebraic seed. Separately listed literal-wrapper obligations remain in D_SOURCE_MAP.')
span('D', 4, 'reviewed_actual_update_identities_and_whole_original_box_denominators_audited',
     ['DBoxDenominators'], 'Actual phase metrics, energies, curvatures and final updated SPD matrix are positive on the whole original box without the root equations. Literal polynomial iff remains separately pending.')
span('D', 9, 'reviewed_actual_infinite_embedded_search_and_literal_Euclidean_nine_query_bound_audited',
     ['DEuclideanLocality'], 'The literal maximum norm of the nine actual trial points also bounds the initial point and controls every phase of every embedded accepted/queried point. The exact source expression tends to zero.')

# Exhaustive I line review; exports are taken from the actual checked inventory.
irows = [
    (1, [], 'Dated editorial record; no mathematical assertion.'),
    (2, [], 'Reading/provenance conventions reviewed; historical execution availability is separately qualified.'),
    (3, ['ObjectiveRun', 'HessianUpdate'], 'Actual full-BFGS and accepted-iterate model; initial SPD only. Three convergence notions and termination/all-ray limitations retained.'),
    (4, [], 'Negative-results heading.'),
    (5, ['DEmbeddingTarget'], 'Actual D C2,1 objective and identity-initialized deterministic local failures with uniform neighborhood and all-query quantifiers.'),
    (6, ['LIdentityTargets', 'LActualCopyTargets'], 'Actual positive-lower-curvature smooth C1,1 and step variants, stable orbit and identity-initialized local copies. No globally C2 plus uniform lower-curvature combination is asserted.'),
    (7, ['AlgebraicSeedCoercive', 'LGlobalTargets'], 'Actual four-affine coercive failure and quadratic-perturbed global failure; true minimizer differs from the bad limit.'),
    (8, [], 'Positive-mechanisms heading.'),
    (9, ['TransportedCertificateConvergence', 'TransportedCertificateVariants', 'RadialConvergence'], 'Actual objective certificate, normalization, band quantifiers and radial implication; strictness/nonnecessity retained in the reviewed G/Q source maps.'),
    (10, ['MovingFrame'], 'Actual comparison energy with the source controlled cumulative transports and inverse transports.'),
    (11, ['ResidualFrames'], 'Actual fixed smooth subspace Hessian/residual criterion; no unproved inclusion of objective classes.'),
    (12, [], 'Concrete-families heading.'),
    (13, ['ReportStructuresEndToEnd', 'ReportFamiliesEndToEnd', 'ReportContinuationEndToEnd', 'MaxAffineBasin'], 'Actual radial/partition/PLQ/centered/powered/transformed families, inactive-piece threshold and exact affine lifting; source qualifications retained.'),
    (14, ['PlanarPrincipalEndToEnd', 'PlanarFiniteMaxTargets'], 'Actual planar cluster/convergence and local nondegenerate finite-max theorems; strict-contour and local-geometry premises retained.'),
    (15, ['RidgeConvergence'], 'Literal ridge supersession now proved, deriving all planar hypotheses and the uniform local basin. Unique attained finite convex minimization supplies compactness without extra coercivity.'),
    (16, ['ParabolicCertificate', 'ReportFamiliesEndToEnd'], 'All original parabolic branches including zero slopes; flat contours and actual eligible-pair radial separation retained.'),
    (17, ['FixedNormalEndToEnd', 'FixedNormalCompositeEndToEnd', 'NormalSpikeVariableTargets'], 'Distinct actual hyperplane/composite/parallel-interface theorems and spike examples; documented nonzero variable-jump parameter qualification.'),
    (18, ['ScalarConvergence', 'ScalarCounterexamples'], 'Scalar arbitrary-positive-metric convergence and actual certificate-nonnecessity objective.'),
    (19, ['HomogeneousDichotomy', 'HomogeneousLowRankConvergence', 'HomogeneousClassCorollaries', 'TwoPieceTargets'], 'Noncompact value dichotomy, actual recurrent/fiber refinements and attributed two-piece theorem. Higher recurrent-rank zero-value iterates are explicitly open.'),
    (20, ['FoundationEndToEnd', 'ObjectiveEndToEnd', 'ObjectiveRates', 'ObjectiveLogRates', 'QuadraticGaugeRates'], 'Actual matrix-derived hierarchy, finite constants and all reciprocal conclusions; exact reference energy/correction and source little-o rates with their hypotheses. No sharpness or evaluation-complexity claim.'),
    (21, ['AffineCriticalDefinability', 'AffineGapTargets', 'IncomingJumpObstruction'], 'Equal-rate geometry, nondegenerate compact gap and incoming-jump obstruction verified. General finite critical components/values and low gap remain pending the finite-path closure; no common BFGS history is inferred from separate incoming pairs.'),
    (22, [], 'Historical 19-job package/counts/timings unverified because original inputs are absent. Explicitly unresolved research boundaries are classified, not promoted to theorems.'),
    (23, ['RidgeConvergence'], 'Supersession implications agree with actual target statements; both negative families and noncompact/flat/distinct-hypothesis results remain. Historical archive availability is separately qualified.'),
]
assert len(irows) == len(mods['I']['coverage_spans']) == 23
for i, files, note in irows:
    state = ('reviewed_mathematical_claims_audited' if files else 'reviewed_editorial_or_scope_statement')
    if i == 21:
        state = 'reviewed_partial_actual_geometry_audited_semialgebraic_finite_values_pending'
    if i == 22:
        state = 'reviewed_historical_execution_unverified_and_explicit_open_boundaries'
    span('I', i, state, files, note)
mods['I'].update(status='synthesis_source_reviewed_semialgebraic_finite_value_and_historical_evidence_claims_open',
                 statement_review='audit/I_SOURCE_RECONCILIATION.md',
                 detailed_inventory='audit/I_SOURCE_RECONCILIATION.md',
                 remaining_claims='A-dependent finite-component/critical-value/low-gap statement at238-249 remains mathematically open. Historical execution/archive assertions at250-259 and provenance references are unverified; literal ridge supersession and all other retained synthesis implications are audited.')

# E is an evidence record, not a collection of replacement mathematical axioms.
for row in mods['E']['coverage_spans']:
    i = int(row['id'].rsplit('.', 1)[1])
    state = 'reviewed_historical_execution_claim_unverified_missing_original_inputs'
    note = 'Literal historical run/count/time/transcript assertion is not Lean-verified; the referenced original execution package is absent. Current universal theorem proofs do not certify those past finite runs.'
    if i in [2, 4]:
        state = 'reviewed_evidential_distinction_or_heading'
        note = 'Read source distinctions between finite calculations, interval certificates, analytic proofs and independent review; no additional theorem or assumption.'
    if i == 24:
        state = 'reviewed_analytic_scope_current_audits_distinguished_from_historical_review'
        note = 'Current compiled proofs supersede draft status only for corresponding verified declarations. Semialgebraic finite-path/value closure remains active; rotating normals, positive-measure/floating-point robustness, a rounded stable-manifold point and blanket semialgebraic convergence remain unclaimed.'
    if i in [25, 26]:
        state = 'reviewed_historical_reproduction_instructions_missing_original_package'
        note = 'Old environment, script/archive hashes and report assembly tools cannot be reproduced from absent inputs. Current Lean reproduction uses pinned bootstrap/check.py and actual delivered manifests/logs; no surrogate is represented as an old job.'
    span('E', i, state, [], note)
mods['E'].update(status='source_evidence_reviewed_historical_execution_not_reproduced_or_Lean_verified',
                 statement_review='audit/HISTORICAL_EVIDENCE_RECONCILIATION.md',
                 remaining_claims='Historical19-job outcomes, exact counts/timings/environment and original script/archive identity lack the referenced inputs. These historical facts remain unverified. Current mathematical conclusions use actual pinned Lean proofs; A path/value closure remains active.')

r['mathematical_corrections'].append(dict(
    id='D.five_nearest_decimal_roundings', source='D.tex141,206,333-334',
    status='actual_precision_and_five_nearest_rounding_corrections_verified',
    correction='All original approximations are within one displayed decimal unit. The corrected nearest values are final point y=-0.004954238005, final Armijo=0.375205963573, final Wolfe=-0.817119670485, scalar center b2=0.468627450980, lower plateau=0.635765118557. Each corrected error is less than half a unit; original source unchanged.',
    review='audit/D_SOURCE_SUPPLEMENT_STATEMENT_REVIEW.md'))
pairs = json.loads((ROOT / 'audit/report_algebra_completion_targets.json').read_text())
assert len(pairs) == 27
e, a = len(s['verified_declarations']), s['audited_declaration_count']
r['milestones'].append(dict(id='report_algebra_completion_15', status='verified',
    targets=[b for _, b in pairs], audit='audit/STATUS.json', statement_review=review,
    explicit_theorems=e, audited_theorems=a, exact_targets=205,
    conditional_infrastructure=['Finite path-cover premise remains explicit',
                               'Actual finite critical-value application remains open',
                               'Historical job records are not theorem proofs']))
r['entire_report_verified'] = False
p.write_text(json.dumps(r, indent=2) + '\n')
marker = '## Fifteenth milestone: general projection, critical definability and source conclusions'
text = f'''\n\n{marker}

The frozen pinned build and full transitive audit passed {e:,} explicit theorems,
{a:,} total theorem declarations, 205 exact targets and 633 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
audit/report_algebra_completion_check.log, STATUS.json and the accompanying
source hashes, actual compiler/axiom logs and statement/independent reviews.

Actual arbitrary-degree Boolean and finite-coordinate semialgebraic projection
is now proved through actual root-index recursion, sign determination and finite
sampling. Actual supporting/affine-critical set/graph definability follows.
The finite semialgebraic smooth-path argument, finite critical values and low gap,
and C's dependent alternative remain open; conditional path-cover statements
are not a proof of those premises.

H's actual three-gradient rank-two sharpness and I's literal ridge supersession
are proved. D's actual numerical precision, original-box update denominators and
literal Euclidean nine-query locality bound are proved, with five documented
nearest-rounding corrections; four immediate literal exports await the next
central gate. I's complete source reconciliation and E's historical-evidence
classification distinguish checked mathematics from absent original run records.
The entire report remains incomplete. Original research sources are unchanged.
'''
for name in ['ENTIRE_REPORT_PLAN.md', 'MATHEMATICAL_REVIEW.md', 'PROOF_OBLIGATIONS.md']:
    p = ROOT / name
    old = p.read_text()
    assert marker not in old
    p.write_text(old + text)
p = ROOT / 'README.md'
old = p.read_text()
old = old.replace('all 4,469 explicit\ntheorems and 6,568 theorem declarations including generated auxiliaries. All 178',
                  f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 205')
old = old.replace('audit/report_geometry_completion_check.log', 'audit/report_algebra_completion_check.log', 1)
old = old.replace("A's general semialgebraic closure, its dependent C alternative, D's remaining\ndisplay precision, and final source/synthesis/evidence reconciliation remain open.",
'''The fifteenth tranche proves actual general semialgebraic projection and actual
supporting/affine-critical graph definability, H's concrete cardinality sharpness,
I's literal ridge supersession, and D's actual display precision, original-box
denominators and exact Euclidean locality. See
[audit/REPORT_ALGEBRA_COMPLETION_STATEMENT_REVIEW.md](audit/REPORT_ALGEBRA_COMPLETION_STATEMENT_REVIEW.md).
A's finite smooth-path/component/critical-value closure and dependent C alternative,
D's last literal wrappers, and final source/evidence reconciliation remain open.''')
old = old.replace('The latest source register records the remaining C/U/A,\nD/L, interpretation, cross-reference and synthesis obligations.',
                  'The latest source register records the remaining A/C path/value,\nD literal-export and historical-evidence obligations.')
p.write_text(old)
print(f'Fifteenth docs/register: {e} explicit/{a} total/205 exact targets; entire report incomplete.')
