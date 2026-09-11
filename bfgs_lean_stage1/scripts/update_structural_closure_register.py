#!/usr/bin/env python3
"""Publish reviewed source coverage only after the complete eleventh audit."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_STRUCTURAL_CLOSURE_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
assert len(s['verified_declarations'])>3004
# Synchronize reviewed scope metadata only; do not rerun or alter proof evidence.
conditions=[('BfgsVerification.LocalStableOrbit.stableOrbit', 'Actual strict derivative with contractive stable block and inverse-contracting unstable block; constructs a forward orbit without assuming one. Source-specific L spectral application remains pending.'), ('BfgsVerification.LocalStableOrbit.positiveStableOrbit', 'Same actual derivative/contraction hypotheses plus a positive stable functional direction; proves positive initial scale. Later scale preservation needs the actual recurrence.'), ('BfgsVerification.LBlockSplitting.positive_orbit_of_block', 'Actual strict derivative, literal upper-block equations and two actual characteristic roots with stated ordering; all coordinates and the forward orbit are constructed. Actual L spectrum/global-run application remains pending.')]
known={d['theorem'] for d in s['verified_declarations']}
for name,condition in conditions:
 assert name in known,name
 s['conditional_results']=[x for x in s['conditional_results'] if x['theorem']!=name]+[dict(theorem=name,verified=True,condition=condition)]
s['outside_verified_scope'][0]='A semialgebraic critical values and rank-loss source closure; C stronger uniform transport and higher-dimensional partial/warning assertions; L actual spectral/global-run application, smooth-manifold regularity and local embeddings; remaining family/source/synthesis/evidence reconciliation. A compact affine gap, C finite-max/quadratic applications and arbitrary rectangular nuclear families are now checked; see REPORT_STATUS.json'
(ROOT/'audit/STATUS.json').write_text(json.dumps(s,indent=2)+'\n')
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text());mods={m['module']:m for m in r['modules']}
review='audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md'
def exports(files):
 out=[d['theorem'] for d in s['verified_declarations'] if any(d['source'].endswith('/'+f+'.lean') for f in files)]
 assert out,files
 return out
def span(tag,i,state,files,note):
 row=next(x for x in mods[tag]['coverage_spans'] if x['id']==f'{tag}.span.{i}')
 row.update(claim_review=state,review_note=note)
 row['verified_exports']=sorted(set(row.get('verified_exports',[])+exports(files)))
mods['A'].update(status='actual_affine_gap_and_local_correctness_verified_semialgebraic_infrastructure_pending',
 statement_review=review+'; audit/A_AFFINE_GAP_VERIFICATION.md; audit/A_AFFINE_GAP_PEER_REVIEW.md',
 remaining_claims='Semialgebraic subdifferential/affine-critical definability and finite critical-value theorem; literal rank-loss Hessian spectrum and final source closure. General-dimensional smooth-max conclusion remains an explicit conjecture, not an unproved claimed theorem. Actual local lower semicontinuity and compact positive-band gap are now verified.')
span('A',3,'reviewed_actual_local_correctness_lower_semicontinuity_and_attained_compact_gap_audited',
 ['AffineDistanceFormula','AffineDistanceContinuity','AffineGapLowerSemicont','AffineGapCompact','AffineGapTargets','AffineGapNeighborhood'],
 'Actual minimum-norm affine point via augmented Gram inverse; rank persistence and fixed-subfamily distance continuity; actual active-set shrinkage and subdifferential equality; lower semicontinuity, local correctness, and an attained strictly positive gap on every nonempty compact positive band. Original-active independence/strict positive weights only; no assumed gap.')
mods['C'].update(status='principal_finite_max_and_explicit_quadratic_basin_separation_verified_further_scope_pending',
 statement_review=review+'; audit/C_FINITE_MAX_VERIFICATION.md; audit/PLANAR_FINITE_MAX_PEER_REVIEW.md; audit/PLANAR_QUADRATIC_STATEMENT_REVIEW.md; audit/PLANAR_QUADRATIC_PEER_REVIEW.md',
 remaining_claims='Semialgebraic alternative; arbitrary-dimensional constant-rank field/secant partial construction and explicit three-dimensional transport warning; stronger all-eligible-pair transversality/log-transport assertions and final source reconciliation. Principal theorem, finite-max application/common actual Hessian sufficient condition, and every printed three-quadratic example assertion are verified.')
for i in [2,11]:
 span('C',i,'reviewed_principal_and_nondegenerate_finite_max_local_basin_audited',
 ['PlanarMaxRegular','PlanarFiniteMaxBasin','HessianStrictConvex','PlanarMaxHessianBasin','PlanarFiniteMaxTargets'],
 'Actual local finite convex C2 maximum, only original-active affine independence/strict optimal weights, derived planar regular charts away from affine criticality and actual local correctness. Objective-only basin precedes every actual BFGS run, arbitrary initial SPD/valid constants. Common positive actual branch Hessian bound derives low strict contours without a contour premise.')
span('C',13,'reviewed_literal_three_quadratic_objective_coefficients_and_exact_basin_audited',
 ['PlanarQuadraticModel','PlanarQuadraticCoefficients','PlanarQuadraticHessian','PlanarQuadraticConvergence','PlanarQuadraticTargets'],
 'Literal triple, actual gradients/Hessians I..3I, average and lower bound sqNorm, unique zero, exact denominator/coefficient formulas with all four closed-box constants and unique positive zero weights. Actual F(x0)<1/100 basin for every full-BFGS run, with all structural premises discharged.')
span('C',14,'reviewed_literal_square_root_curve_and_fixed_band_eligible_radial_separation_audited',
 ['PlanarQuadraticCurve','PlanarQuadraticPairs','PlanarQuadraticSeparation','PlanarQuadraticTargets'],
 'Actual square-root tie, O(u^3) expansion, strict active pair/third inactivity, actual gradients, exact d/t/decrease and radial numerator, derived c1=1/4 c2=1/2 eligibility, quotient tending to infinity. In every neighborhood a fixed eta precedes every delta/C; actual SPD single-step realization is proved. No divergent trajectory claim.')
mods['R'].update(status='radial_theorems_and_rectangular_nuclear_named_families_verified_final_source_review_pending',
 statement_review=review+'; audit/RECTANGULAR_NUCLEAR_STATEMENT_REVIEW.md; audit/RECTANGULAR_NUCLEAR_PEER_REVIEW.md',
 remaining_claims='Final named-family/source/evidence reconciliation, including the explicitly unresolved historical old four-piece optimizer attribution. Arbitrary rectangular nuclear norm, centered convergence, mixed powers, literal first differences and previously verified spectral/radial boundary models are now closed.')
span('R',10,'reviewed_sublinear_mixed_powers_and_actual_rectangular_nuclear_family_audited',
 ['NuclearGram','NuclearVariational','NuclearNormFacts','CenteredRectangularNuclear','RectangularNuclearTargets'],
 'Actual sum of square roots of Gram eigenvalues equals actual PSD square-root trace and spectral-contraction variational supremum with an attaining polar witness, including rank/dimension zero. Norm and convexity properties are derived, then actual centered full-BFGS convergence, zero inward error, radial bounds and finite mixed nuclear-power families follow.')
span('R',11,'reviewed_named_scalar_residual_and_literal_first_difference_basins_audited',
 ['FirstDifferencePenalty','RectangularNuclearTargets'],
 'Literal first-difference matrix and weighted absolute-value sum, zero/nonzero optimal residual decomposition, objective-only local basin around any unique optimizer for every actual run. No zero-minimizer or fixed initial metric restriction.')
span('R',16,'reviewed_actual_spectral_nuclear_boundary_and_arbitrary_rectangular_norm_audited',
 ['NuclearGram','NuclearVariational','NuclearNormFacts','CenteredRectangularNuclear','RectangularNuclearTargets'],
 'Earlier actual symmetric 2x2 nonzero-rank-deficient radial-boundary example remains distinct from the now checked arbitrary rectangular nuclear norm and centered family. No BFGS failure conclusion is inferred from the radial-boundary pair.')
mods['L'].update(status='actual_return_oracle_and_constructive_dynamics_criteria_verified_spectral_application_embeddings_pending',
 statement_review=review+'; audit/L_NORMALIZED_RETURN_STATEMENT_REVIEW.md; audit/L_NORMALIZED_ORACLE_STATEMENT_REVIEW.md; audit/LOCAL_STABLE_ORBIT_STATEMENT_REVIEW.md; audit/L_BLOCK_SPLITTING_STATEMENT_REVIEW.md; audit/L_BLOCK_SPLITTING_PEER_REVIEW.md',
 remaining_claims='Actual shape derivative and kernel-certified spectral intervals, application to an infinite actual perturbed deterministic BFGS run/global failure; smooth two-dimensional stable-manifold/tangency and local-diffeomorphism ancillary assertions; C1,1 and countably affine scalar/local embeddings, identity initialization, actual Hessian bounds and final source closure. Constructive orbit criteria remain conditional on the actual strict derivative and spectral data; no assumed orbit is added.')
span('L',4,'reviewed_actual_normalized_return_and_positive_scale_implementation_neighborhood_audited',
 ['LNormalizedReturn','LNormalizedOracle'],
 'Literal fixed-input-scale three-step inverse-BFGS recursion, analytic return with nonzero positive denominators near exact fixed seed, actual gradients/value scaling, all nine deterministic query derivatives/decisions/histories, actual physical point/matrix updates and final normalization. The one neighborhood is derived, with positive physical scale explicit; no orbit permanence assumed.')
span('L',5,'reviewed_actual_point_columns_last_row_and_conditional_constructive_splitting_orbit_audited_spectral_application_pending',
 ['LNormalizedReturn','StableSequenceTransform','StableSequenceEstimates','StableSequence','LocalStableOrbit',
  'StablePositiveDirection','StableOrbitTargets','LBlockBasis','LDiagonal','LBlockEigen','LBlockConjugacy','LBlockColumns','LPositiveOrbit','LBlockStableOrbit'],
 'Actual rho^-1 point columns and rho last row checked. Conditional algebra derives explicit eigenvectors, actual invertible coordinates and ordinary-norm contraction bounds from two actual J roots; conditional C0 contraction constructs actual forward orbits with freely prescribed stable start and positive initial physical scale in every neighborhood. Actual J certificate/application and stronger smooth-manifold/local-diffeomorphism assertions remain separate. Direct orbit proof replaces the source manifold route for trajectory existence without claiming manifold regularity.')
pairs=json.loads((ROOT/'audit/report_structural_closure_targets.json').read_text())
r['milestones']=[m for m in r['milestones'] if m['id']!='report_structural_closure_11']+[dict(
 id='report_structural_closure_11',status='verified',targets=[p[1] for p in pairs],audit='audit/STATUS.json',
 statement_review=review,explicit_theorems=len(s['verified_declarations']),audited_theorems=s['audited_declaration_count'],
 exact_targets=120,conditional_criteria=['BfgsVerification.LocalStableOrbit.stableOrbit','BfgsVerification.LocalStableOrbit.positiveStableOrbit'])]
r['entire_report_verified']=False
p.write_text(json.dumps(r,indent=2)+'\n')
print('Eleventh reviewed source register updated; 120 exact targets; entire report remains incomplete.')
