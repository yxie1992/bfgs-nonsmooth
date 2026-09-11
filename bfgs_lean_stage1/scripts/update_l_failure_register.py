#!/usr/bin/env python3
"""Publish reviewed twelfth source coverage only after the complete pinned audit."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_L_FAILURE_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
assert len(s['verified_declarations'])>3346
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text());mods={m['module']:m for m in r['modules']}
review='audit/REPORT_L_FAILURE_STATEMENT_REVIEW.md'
def exports(files):
 out=[d['theorem'] for d in s['verified_declarations'] if any(d['source'].endswith('/'+f+'.lean') for f in files)]
 assert out,files
 return out
def span(tag,i,state,files,note):
 row=next(x for x in mods[tag]['coverage_spans'] if x['id']==f'{tag}.span.{i}')
 row.update(claim_review=state,review_note=note)
 if files:row['verified_exports']=sorted(set(row.get('verified_exports',[])+exports(files)))
mods['A'].update(status='actual_affine_gap_path_calculus_and_special_polynomial_projection_verified_general_semialgebraic_closure_pending',
 statement_review=review+'; audit/A_SUPPORT_PATH_VERIFICATION.md; audit/A_SEMIALGEBRAIC_REDUCTION_VERIFICATION.md; audit/A_LINEAR_PROJECTION_VERIFICATION.md',
 remaining_claims='General nonlinear polynomial quantifier elimination/projection and finite semialgebraic path decomposition; their actual support/affine-critical definability and finite critical-value application; literal rank-loss Hessian spectrum and final source reconciliation. Path calculus, bounded signed supports, genuine polynomial syntax/support-graph reduction and Boolean affine-coordinate projection are verified. The general-dimensional smooth-max convergence assertion is explicitly a conjecture.')
span('A',4,'reviewed_actual_path_support_and_special_projection_infrastructure_general_semialgebraic_application_pending',
 ['AffineCriticalPathCover','SemialgebraicSupportProjection','SemialgebraicAffineTargets'],
 'Actual all-support path derivative and constancy, signed at-most-n+1 support representation, conditional finite actual path cover to finite critical values/gap; genuine polynomial Boolean syntax and actual support-graph projection reduction; exact affine-coordinate Boolean elimination. General nonlinear projection and path-component decomposition remain obligations, so the source semialgebraic proposition is not marked verified.')
span('A',5,'reviewed_explicit_conjecture_not_asserted_as_theorem',[],
 'Read and retained as an explicit general-dimensional convergence conjecture. The verified planar/fixed-normal cases are not promoted to a proof; nonlinear coordinate straightening is not used as ordinary BFGS invariance.')
mods['C'].update(status='principal_finite_max_quadratic_and_spatial_warning_verified_uniform_and_higher_dimensional_partial_scope_pending',
 statement_review=review+'; audit/C_SPATIAL_WARNING_VERIFICATION.md; audit/C_SPATIAL_WARNING_PEER_REVIEW.md',
 remaining_claims='Semialgebraic alternative depends on A; arbitrary-dimensional constant-rank field/secant partial construction; stronger all-eligible-pair transversality/log-transport assertions and final source reconciliation. Actual principal, finite-max/quadratic applications and literal three-dimensional transport warning are verified.')
span('C',15,'reviewed_literal_three_dimensional_quadratic_warning_and_actual_radial_convergence_audited',
 ['SpatialQuadraticTargets'],
 'Actual Q=diag(1,2,3), printed step and gradients, exact decrease/curvature/determinant, strict eligibility and SPD single-step realization; canonical equal-rate field and failure of projected Loewner transport for every finite multiplier. Actual radial certificate/full-BFGS convergence on the same quadratic; no divergent-trajectory conclusion.')
mods['L'].update(status='actual_global_failure_and_both_fixed_spd_local_failures_verified_identity_and_smooth_manifold_pending',
 statement_review=review+'; audit/L_RETURN_DYNAMICS_PEER_REVIEW.md; audit/L_ACTUAL_COPIES_INDEPENDENT_REVIEW.md',
 remaining_claims='One fixed affine square-root normalization to identity initialization, transformed strong-convexity/Lipschitz/Hessian constants and full-search/whole-family transfer; smooth two-dimensional stable-manifold regularity/tangency; final source/synthesis/evidence reconciliation. Actual global Q_mu failure and both literal fixed-SPD local-copy failure families have no remaining trajectory, spectral, oracle or limit premise.')
span('L',1,'reviewed_preamble_not_a_mathematical_assertion',[],
 'TeX notation/counter preamble only; substantive assertions begin in the following span.')
span('L',2,'reviewed_actual_global_theorem_and_fixed_spd_local_failure_identity_initialization_pending',
 ['LQuadraticSeed','LGlobalTargets','LActualCopyTargets'],
 'Literal deterministic full inverse-BFGS implementation and strict margins; actual mu>0 global failure with all quadratic seed geometry, three constant branch Hessians and arbitrary small physical queries. Both literal local failures now constructed with one fixed SPD matrix; the displayed H0=I theorem awaits the fixed affine normalization.')
span('L',5,'reviewed_actual_spectrum_hyperbolicity_inverse_and_global_orbit_audited_smooth_manifold_pending',
 ['LShapeDerivative','LShapeIntervalCertificate','LShapeSpectrum','LReturnSpectrum','LReturnParameterBlock','LReturnLocalInverse','LReturnStableOrbit','LGlobalFailure','LGlobalTargets','LFlattenNeighborhood'],
 'Actual Jet differentiation and exact kernel rational interval certificate; actual full characteristic polynomial/multiplicity, parameter block, no complex unit-circle eigenvalue, actual local inverse; constructive positive actual return orbit and all-phase actual BFGS failure in every physical neighborhood. Smooth-manifold regularity/tangency remains a separate source assertion, not inferred from existential orbits.')
span('L',6,'reviewed_literal_smooth_scalar_and_four_branch_geometry_actual_hessian_bounds_audited',
 ['LScalarTargets','LEmbeddingGeometryTargets','LEmbeddingSourceDetails','FiniteMaxHessianTargets'],
 'Actual scalar formula, global C1,1, C2 off0/not twice differentiable0, all nodes/half-scale plateaus/curvature bounds; actual literal objective with source439/446/27 and512 Euclidean bounds, mu strong convexity, unique nonsmooth0/compact sublevels/directional derivative, actual finite-max Hessian bounds and explicit fourth Hessian mu I.')
span('L',7,'reviewed_actual_all_scale_local_copy_run_families_audited_fixed_identity_normalization_pending',
 ['LEmbeddingLocal','LSeedCopies','ScaledCopyRun','ScaledCopyQueries','TranslatedSearch','LActualCopies','LActualCopyLocality','LActualCopyTargets'],
 'Fixed open chart exact local identity at all scales; actual source orbit selected inside it; original full BFGS and every deterministic rejection/acceptance transferred exactly. One fixed SPD initial matrix, positive nonstationary limits, strict value decrease, starts to0 and uniform all-query neighborhood containment. Fixed affine identity initialization remains subsequent work.')
span('L',8,'reviewed_literal_step_scalar_countable_polyhedral_hessian_and_actual_fixed_spd_failure_audited',
 ['LScalarStepTargets','LStepEmbeddingTargets','LActualCopyTargets'],
 'Actual step ramp/countable attained affine envelope, local finite polyhedrality off0 from zero-argument inactivity, local affinity at actual differentiability points and literal Hessian mu I; same exact local copies and actual fixed-SPD bad-run family. The final displayed transformed Hessian awaits fixed affine whitening.')
pairs=json.loads((ROOT/'audit/report_l_failure_targets.json').read_text())
r['milestones']=[m for m in r['milestones'] if m['id']!='report_l_failure_12']+[dict(
 id='report_l_failure_12',status='verified',targets=[p[1] for p in pairs],audit='audit/STATUS.json',statement_review=review,
 explicit_theorems=len(s['verified_declarations']),audited_theorems=s['audited_declaration_count'],exact_targets=145,
 conditional_infrastructure=['A finite actual path-cover criterion','A special affine-coordinate projection, without general nonlinear QE','generic finite-max actual Hessian calculus','translated/scaled run interfaces, discharged in the two L local-copy targets'])]
r['entire_report_verified']=False
p.write_text(json.dumps(r,indent=2)+'\n')
print('Twelfth source register updated after full audit;145 exact targets; entire report remains incomplete.')
