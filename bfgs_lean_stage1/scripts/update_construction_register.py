#!/usr/bin/env python3
"""Apply the reviewed ninth tranche only after its complete build/axiom audit."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
status = json.loads((ROOT / 'audit/STATUS.json').read_text())
assert status['status'] == 'MODULE_M_AND_REPORT_CONSTRUCTION_TARGETS_VERIFIED'
assert not status['unexpected_axioms'] and not status['missing_axiom_reports']
assert not status['remaining_target_obligations']
assert len(status['verified_declarations']) > 2193
path = ROOT / 'audit/REPORT_STATUS.json'
register = json.loads(path.read_text())
modules = {m['module']: m for m in register['modules']}
review = 'audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md'

def exports(*files):
    result = [d['theorem'] for d in status['verified_declarations']
              if any(d['source'].endswith('/' + f + '.lean') for f in files)]
    assert result, files
    return result

def span(tag, number, state, files, note):
    row = next(s for s in modules[tag]['coverage_spans'] if s['id'] == f'{tag}.span.{number}')
    row['claim_review'] = state
    row['verified_exports'] = sorted(set(row.get('verified_exports', []) + exports(*files)))
    row['review_note'] = note

modules['D'].update(
    status='actual_coercive_seed_and_complete_scalar_construction_verified_local_embedding_pending',
    statement_review=review + '; audit/COERCIVE_SEED_STATEMENT_REVIEW.md; audit/D_SCALAR_ASSEMBLY_PEER_REVIEW.md',
    remaining_claims='The actual two-dimensional C2,1 max-branch objective, its uniform Hessian constants, local model, starts approaching the minimizer, and all infinite accepted/rejected embedded trials. The scalar functions themselves and the separate coercive max-affine seed are now checked.')
span('D', 6, 'reviewed_actual_coercive_deterministic_counterexample_audited',
     ['AlgebraicSeedCoercive', 'CoerciveSeedIntercept', 'ReportConstructionEndToEnd'],
     'Actual four-piece objective, unique optimizer(-1,16), compact sublevels, actual full-BFGS run and all deterministic searches; value/iterate limits and nonstationarity derived. No assumed limit or added update.')
span('D', 7, 'reviewed_complete_scalar_lemma_and_global_C21_construction_audited',
     ['DScalarRamp', 'DScalarGeometric', 'DScalarSeries', 'DScalarIntervals', 'DScalarCurvature',
      'DScalarJets', 'DScalarPlateaus', 'DScalarNegative', 'DScalarAssembly', 'DScalarTarget'],
     'Actual literal ramp/primitive, geometric series equal to every printed region, actual first/second derivatives and C2 at all joins including zero, sharp curvature and Lipschitz constants, coercivity/unique zero, exact node jets and closed half-scale plateaus. Uniform2<=b<=34 covers both source parameters. Geometric-series differentiation replaces the source asymptotic proof route without assuming interpolation or smoothness.')

modules['C'].update(
    status='actual_visible_field_and_full_BFGS_tail_log_transport_verified_secant_main_pending',
    statement_review=review + '; audit/C_ACTUAL_TRANSPORT_VERIFICATION.md',
    remaining_claims='Crossing secant correction, full C contradiction and local/example consequences; stronger uniform all-eligible-pair variant. Source-only actual-run logarithmic transport, uniform visibility/transversality and all corner/right-derivative inputs are now derived.')
span('C', 7, 'reviewed_actual_field_visibility_buffer_and_derivative_bounds_audited',
     ['PlanarFieldBuffer', 'PlanarFieldTangency'],
     'Compact nested buffers, uniform close-pair Lipschitz bounds, actual derivative norm bounds, and actual preservation of level tangents; no assumed triangular derivative matrix.')
span('C', 8, 'reviewed_actual_determinant_and_one_sided_transport_calculus_audited',
     ['PlanarDerivativeDeterminant', 'PlanarScalarTransport'],
     'Literal determinant derivative estimate with actual finite-Pi operator norm constants; right-derivative convex/log comparison avoids a finite-switching or a.e.-FTC assumption.')
span('C', 9, 'reviewed_actual_tail_transversality_and_log_transport_audited_secant_pending',
     ['PlanarTransversality', 'PlanarRunTransversality', 'PlanarFieldStructure',
      'PlanarCornerTransport', 'PlanarEndpointTransport', 'PlanarRunTransport'],
     'One coherent actual cutoff/velocity family works through smooth and corner points. Actual-run source wrapper derives positive limiting gap and vanishing steps from compactness/strict contours/no affine-critical cluster, and retains uniformly positive visibility. Crossing secant and stronger all-eligible-pair uniform statement remain separate.')

modules['U'].update(
    status='principal_composite_theorems_and_literal_spike_objective_oracle_verified_variable_jump_pending',
    statement_review=review + '; audit/NORMAL_SPIKE_EXAMPLE_PEER_REVIEW.md',
    remaining_claims='Variable-jump c!=0 non-additive example and its actual local-run/radial-separation conclusions. The scalar spike, all-dimensional objective, actual Hessian peaks, every-neighborhood RS failure, and universally correct terminating rational value/first/second-derivative oracle are now checked. Separate historical Python experiment correspondence is evidence, not a proof premise.')
span('U', 12, 'reviewed_actual_infinite_spike_and_all_dimensional_example_audited',
     ['NormalSpikeBump', 'NormalSpikeScaled', 'NormalSpikeSeries', 'NormalSpikeGeometry',
      'NormalSpikeBounds', 'NormalSpikeRegularity', 'NormalSpikeMassSupport', 'NormalSpikeTargets',
      'NormalSpikeObjective', 'NormalSpikeGradient', 'NormalSpikeRadialBound', 'NormalSpikeSamples',
      'NormalSpikeSeparation', 'NormalSpikeInterface', 'NormalSpikeHessian', 'NormalSpikeExampleTargets'],
     'Actual integral/series, globalC1/C3offzero, actual second derivative atzero and unbounded peaks, mass/support geometry; printed arbitrary-dimensional strongly convex objective, exact nonsmooth hyperplane/tangential supports, fullBFGS value/iterate convergence, actual Hessian peaks, and RS failure on every neighborhood/positive sublevel. No assumed oracle or Hessian limit.')
span('U', 13, 'reviewed_actual_infinite_series_oracle_and_executable_rational_program_audited',
     ['NormalSpikeOracle', 'NormalSpikeRational'],
     'Exact finite-prefix/geometric-tail identities for arbitrary queries; terminating rational search and computable value/first/second derivative program proved universally equal to the actual integral-defined source function. No unchecked external computation.')

modules['R'].update(
    statement_review=review + '; audit/R_FAMILY_COVERAGE_MAP.md',
    remaining_claims='General-dimensional nuclear norm identification and remaining descriptive family identities/cross-references. The older(-1,5),25/4 four-piece attribution has no recoverable objective in preserved sources/history; it is explicitly unresolved historical evidence. A checked current-D supporting-plane correction is provided. Singular a.e. curvature caveat, norm-scaled IR convention, and actual arbitrary rectangular spectral norm are now verified.')
span('R', 3, 'reviewed_inward_equivalence_and_norm_scaled_convention_audited',
     ['RadialNormConvention'],
     'Actual positive-band radius lower bound and compact upper bound absorb the Euclidean radius-squared factor with correct uniform constants and quantifier order.')
span('R', 6, 'reviewed_actual_radial_Hessian_and_singular_curvature_caveat_audited',
     ['RadialSingularCurvature', 'ReportConstructionEndToEnd'],
     'Actual strongly convex shifted-absolute objective, compact sublevel, uniformly bounded a.e. classical radial Hessian on the whole sublevel, yet actual RS failure. This preserves the distinction between classical a.e. curvature and singular curvature.')
span('R', 7, 'reviewed_current_model_supporting_plane_correction_audited_historical_attribution_unresolved',
     ['CoerciveSeedIntercept'],
     'For the actual currentD objective optimizer(-1,16), heights0,0,-1+c-16d and actual secant curvature->0 are checked; RS/SP fail on actual initial sublevel. Printed(-1,5) is proved not its optimizer. Older source reference remains explicitly unresolved; no missing objective is invented.')
span('R', 16, 'reviewed_arbitrary_rectangular_spectral_norm_and_2x2_nuclear_model_audited_general_nuclear_pending',
     ['CenteredSpectral'],
     'Actual Euclidean operator/spectral norm, arbitrary rectangular coordinates and exact Frobenius pairing, compact sublevels and unique zero, zero IR error, RS and actual fullBFGS convergence. General-dimensional nuclear model remains separate.')

correction_id = 'R.historical_four_piece_attribution'
if not any(c['id'] == correction_id for c in register['mathematical_corrections']):
    register['mathematical_corrections'].append(dict(
        id=correction_id, source='R.tex182-187 compared with D.tex231-245',
        status='current_model_correction_verified_historical_attribution_unresolved',
        correction='CurrentD optimizer is(-1,16), and actual supporting heights are0,0,-1+c-16d. At printed(-1,5), currentF>=3/8. The older25/4 example lacks a recoverable definition; preserve it as unresolved historical evidence, not a verified current-model claim.',
        review='audit/COERCIVE_SEED_INTERCEPT_CORRECTION.md'))
for correction in register['mathematical_corrections']:
    if correction['id'] == 'C.negative_orientation_transport_sign':
        correction['status'] = 'corrected_algebra_actual_field_and_full_BFGS_tail_transport_verified_secant_pending'

targets = ['BfgsVerification.' + t for t in
           ['coerciveSeedFailure', 'dScalarFunction', 'centeredSpectralConvergence', 'singularCurvatureCounterexample']]
targets += ['BfgsVerification.NormalSpike.' + t for t in
            ['sourceSpikeProperties', 'spikeObjectiveConvergence', 'spikeRadialSeparation',
             'spikeObjectiveGeometry', 'spikeHessianPeaks', 'rationalSpikeOracle']]
register['milestones'] = [m for m in register['milestones'] if m['id'] != 'report_construction_9'] + [dict(
    id='report_construction_9', status='verified', targets=targets, audit='audit/STATUS.json',
    statement_review=review, explicit_theorems=len(status['verified_declarations']),
    audited_theorems=status['audited_declaration_count'], exact_targets=95)]
register['entire_report_verified'] = False
path.write_text(json.dumps(register, indent=2) + '\n')
print('Ninth reviewed source register updated; entire report remains incomplete.')
