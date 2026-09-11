#!/usr/bin/env python3
"""Publish thirteenth source coverage only after the frozen full audit passes."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_SOURCE_CLOSURE_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_source_closure_source_hashes.json').read_text())
assert len(hashes)==543
for f,h in hashes.items():
    assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text());mods={m['module']:m for m in r['modules']}
review='audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md'
def exports(files):
    for f in files: assert (ROOT/'BfgsVerification'/(f+'.lean')).is_file(),f
    out=[d['theorem'] for d in s['verified_declarations'] if any(d['source'].endswith('/'+f+'.lean') for f in files)]
    assert out,files
    return out
def span(tag,i,state,files,note):
    row=next(x for x in mods[tag]['coverage_spans'] if x['id']==f'{tag}.span.{i}')
    row.update(claim_review=state,review_note=note)
    row.pop('verification_note',None)
    if files:row['verified_exports']=sorted(set(row.get('verified_exports',[])+exports(files)))
for tag in ['T','G','C']:
    span(tag,1,'reviewed_preamble_not_a_mathematical_assertion',[],
         'Read original source: TeX notation and counters only; no mathematical claim.')
mods['T'].update(status='verified',remaining_claims=[],statement_review='audit/TF_SOURCE_DETAILS_STATEMENT_REVIEW.md')
span('T',7,'reviewed_all_retained_claims_audited',
     ['ComparisonEnergyWarning','ParabolicCertificate','ParabolicExampleSeparation','ParabolicExampleContrast','ParabolicScalarTransport','AffineCertificates'],
     'Actual Q certificate/printed field and eligible radial separation complete strict inclusion; radial inclusion and full affine covariance already audited. Explicit SPD energy countermodel verifies the final small-vector-change inference warning; no BFGS trajectory is claimed for that algebraic countermodel.')
mods['F'].update(status='verified_with_documented_line_search_proof_replacement',remaining_claims=[],
                statement_review='audit/TF_SOURCE_DETAILS_STATEMENT_REVIEW.md; audit/TF_SOURCE_DETAILS_INDEPENDENT_REVIEW.md')
span('F',4,'reviewed_all_retained_claims_audited',
     ['ScalarResidualFamilies','EuclideanResidualRadial','AffineImageRanges','AffineLifting'],
     'Actual scalar and Euclidean residual decompositions/basins and actual projected full-BFGS lifting; exact range(H_k A^T)=range(H_0 A^T) now checked. Projected convergence is the explicit source lifting premise; full-space convergence and metric-fiber selection are derived.')
mods['G'].update(status='verified_with_documented_accessible_active_span_correction',remaining_claims=[],
                statement_review='audit/G_SOURCE_CLOSURE_REVIEW.md; audit/G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md')
span('G',2,'reviewed_definitions_and_cross_module_claims_audited',
     ['TransportedCertificateRun','TransportedCertificateConvergence','TransportedCertificateVariants','CompactSolutionBasin'],
     'Actual endpoint/certificate definitions and accepted-pair bridge; positive curvature and nonzero step; T objective, solution-set, unique iterate, local and nonunique-neighborhood conclusions.')
span('G',7,'reviewed_corrected_claims_and_actual_counterexample_audited',
     ['AccessibleJumpGeometry','AccessibleCurvatureBridge','ShiftedAbsAccessibility'],
     'Accessible-span tangency/visibility and the all-active affine-span identity are proved distinctly. The unqualified inference from accessible annihilation to full-active tangency is false; actual shiftedAbs at (1/8,1/4) has constant-I certificates and zero accessible jumps but zero full-active tangent. The incorrect literal inference is not marked proved.')
mods['A'].update(status='actual_affine_geometry_rank_loss_and_local_semialgebraic_infrastructure_verified_general_closure_pending',
                statement_review=review+'; audit/A_UNIVARIATE_CELLS_VERIFICATION.md; audit/A_POLYNOMIAL_SIMPLE_ROOT_VERIFICATION.md',
                remaining_claims='General nonlinear polynomial projection/quantifier elimination, finite semialgebraic piecewise-C1 path decomposition, and the actual support/affine-critical definability/finite-value application. Genuine one-dimensional cells and arbitrary-degree simple-root local charts/projection are verified infrastructure, not the general theorem. The general-dimensional smooth-max convergence assertion is an explicit conjecture.')
span('A',2,'reviewed_all_literal_rank_loss_geometry_and_hessian_spectrum_audited',
     ['AffineRankLossHessian','AffineRankLossTargets'],
     'Actual branch Hessians, eigenvalues exactly1 and3, smoothness/strong convexity and objective strong convexity now complete the literal example; actual subdifferential/rank-loss/positive-gap geometry was already audited.')
span('A',4,'reviewed_path_and_local_semialgebraic_infrastructure_general_application_pending',
     ['UnivariateCellTargets','PolynomialRootTargets'],
     'Actual univariate finite semialgebraic convex cells, sign boundaries, arbitrary-degree polynomial fiber derivatives and simple-root C-infinity charts/local projection now join the path/signed-support/affine-coordinate infrastructure. General nonlinear projection and higher-dimensional path decomposition remain genuine obligations.')
mods['C'].update(status='principal_theorems_and_uniform_same_field_endpoint_estimates_verified_higher_dimensional_and_semialgebraic_scope_pending',
                statement_review=review+'; audit/C_ALL_ENDPOINTS_STATEMENT_REVIEW.md; audit/C_ALL_ENDPOINTS_INDEPENDENT_PEER_REVIEW.md',
                remaining_claims='A-dependent semialgebraic alternative; arbitrary-dimensional actual constant-rank common-rate field and secant construction; final source reconciliation. All three stronger uniform estimates now hold for one actual constructed field and every sufficiently close eligible endpoint pair, with no run-dependent premises.')
span('C',3,'reviewed_actual_canonical_geometry_and_cluster_reduction_audited',
     ['AffineCriticalObjective'],
     'Actual minimum-norm point of affine hull of the full convex subdifferential, equal pairing/rate, stationarity/minimum equivalence, and compact actual-run cluster-to-value/solution-set/unique-iterate conclusions. No gradient convergence assumed.')
span('C',4,'reviewed_actual_run_budget_and_strict_contour_steps_audited',
     ['StrictContours','TransportedCertificateRun'],
     'Actual accepted-pair inequalities, derived Armijo summability and compact gradient bounds from M; actual strict-contour vanishing steps. No pre-existing iterate limit or singleton cluster set assumption.')
span('C',5,'reviewed_geometric_construction_setup_not_separate_assertion',[],
     'Heading and compact regular level-set setup; the following geometric and uniform endpoint constructions discharge its stated setting.')
span('C',9,'reviewed_uniform_same_field_all_eligible_endpoint_estimates_audited',
     ['PlanarAllEndpointField','PlanarAllEndpoints','PlanarAllEndpointTargets','PlanarAllPairTargets'],
     'One actual finite-corner comparison field, with constants and neighborhoods chosen before every sufficiently close eligible pair, simultaneously has all-segment transversality, secant correction, positive transport factor, absolute log bound and square-factor bound. Actual Euclidean endpoint length; no trajectory or common limit premise.')
mods['L'].update(status='actual_global_and_identity_local_failure_theorems_and_smooth_invariant_manifold_verified_final_precision_reconciliation_pending',
                statement_review=review+'; audit/L_IDENTITY_STATEMENT_REVIEW.md; audit/L_STABLE_MANIFOLD_STATEMENT_REVIEW.md; audit/L_STABLE_MANIFOLD_PEER_REVIEW.md',
                remaining_claims='Final line-by-line source/evidence reconciliation, including exact scope of printed high-precision approximate Jacobian entries. All principal global/local failure, fixed identity initialization, transformed geometry and actual smooth stable-manifold/tangency/local-invariance assertions are proved; no trajectory, spectral or limit premise remains.')
span('L',2,'reviewed_actual_global_and_identity_initialized_local_failure_theorems_audited',
     ['LIdentityRuns','LIdentityTargets','LIdentityGeometry'],
     'Both literal fixed-objective local failure families now use H0=I through one actual fixed SPD square root. Every deterministic search history, strict AWW, all actual query derivatives, positive nonstationary limits, starts to0 and uniform all-query containment are derived.')
span('L',5,'reviewed_actual_spectrum_inverse_and_smooth_invariant_manifold_audited_display_precision_reconciliation_pending',
     ['LStableManifoldTargets','LStableInvariantManifold'],
     'Actual smooth embedded two-dimensional graph, rank-two derivative equal to actual linear stable space, arbitrary positive physical scale, actual forward orbits staying in every prescribed neighborhood and converging, plus local forward invariance of the same graph. Source approximate15-digit display requires a separate precision check; actual spectral signs and exact Jacobian/parameter identities are already checked.')
span('L',7,'reviewed_fixed_identity_all_scale_local_failure_and_transformed_geometry_audited',
     ['AffineWhiteningSquareRoot','AffineWhiteningSearch','AffineWhiteningHessian','LIdentityGeometry'],
     'One fixed A=H0^(1/2), exact all-fuel search covariance, actual transformed derivatives/Hessians and sharp eigenvalue-based constants; one fixed objective in each family, arbitrary-neighborhood local failure with H0=I.')
span('L',8,'reviewed_step_polyhedral_geometry_actual_transformed_hessian_and_identity_failure_audited',
     ['LIdentityGeometry','LWhiteningGeometry'],
     'Actual countable attained affine residual after the fixed map, actual Hessian mu H0 at every differentiability point and spectral bounds; fixed identity initialized full-BFGS bad-run family with all source limiting/locality conclusions.')
pairs=json.loads((ROOT/'audit/report_source_closure_targets.json').read_text())
r['milestones']=[m for m in r['milestones'] if m['id']!='report_source_closure_13']+[dict(
    id='report_source_closure_13',status='verified',targets=[x[1] for x in pairs],audit='audit/STATUS.json',statement_review=review,
    explicit_theorems=len(s['verified_declarations']),audited_theorems=s['audited_declaration_count'],exact_targets=162,
    conditional_infrastructure=['Univariate cells and local simple-root projection do not prove general nonlinear projection','Generic fixed-point/stable-graph infrastructure has its actual L hypotheses discharged','Affine lifting retains the literal projected convergence premise'])]
r['entire_report_verified']=False
p.write_text(json.dumps(r,indent=2)+'\n')
print('Thirteenth source coverage published after frozen full audit; entire report remains incomplete.')
