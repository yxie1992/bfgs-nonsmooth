#!/usr/bin/env python3
"""Apply the reviewed tenth tranche only after its complete build/axiom audit."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
status = json.loads((ROOT/'audit/STATUS.json').read_text())
assert status['status'] == 'MODULE_M_AND_REPORT_EMBEDDING_TARGETS_VERIFIED'
assert not status['unexpected_axioms'] and not status['missing_axiom_reports']
assert not status['remaining_target_obligations']
assert len(status['verified_declarations']) > 2718
path = ROOT/'audit/REPORT_STATUS.json'
r = json.loads(path.read_text())
modules = {m['module']: m for m in r['modules']}
review = 'audit/REPORT_EMBEDDING_STATEMENT_REVIEW.md'

def exports(*files):
    result = [d['theorem'] for d in status['verified_declarations']
              if any(d['source'].endswith('/'+f+'.lean') for f in files)]
    assert result, files
    return result

def span(tag, number, state, files, note):
    row = next(s for s in modules[tag]['coverage_spans'] if s['id']==f'{tag}.span.{number}')
    row['claim_review'] = state
    row['verified_exports'] = sorted(set(row.get('verified_exports', [])+exports(*files)))
    row['review_note'] = note

modules['D'].update(
    status='actual_C21_objective_and_complete_deterministic_embedding_verified',
    statement_review=review+'; audit/D_EMBEDDING_STATEMENT_REVIEW.md; audit/D_EMBEDDING_PEER_REVIEW.md',
    remaining_claims='No remaining proof premise in D main/scalar/seed/local-embedding construction. Historical numerical display precision and cross-reference evidence remain subject to the final report synthesis/evidence review; original source unchanged.')
row=modules['D']['coverage_spans'][0]
row.update(claim_review='reviewed_tex_preamble_no_mathematical_claim', review_note='Only TeX macros/counters; no mathematical assertion.')
span('D',2,'reviewed_actual_main_objective_and_deterministic_embedding_audited',
     ['DEmbeddingObjective','DEmbeddingRun','DEmbeddingLocalization','DEmbeddingTarget','ReportEmbeddingEndToEnd'],
     'Actual fixed four-branch globally C2,1 objective, all Hessians0..64I, unique nonsmooth minimizer, same physical point/matrix trajectories for every valid source c1,c2, actual search histories at all k, all trial differentiability, nonstationary limit and uniform whole-trajectory localization. No assigned oracle choices or assumed convergence.')
span('D',7,'reviewed_complete_scalar_construction_actual_derivatives_and_asymptotic_orders_audited',
     ['DScalarPlateauDerivative','DScalarSmallBounds'],
     'Adds actual plateau derivatives and explicit right-zero phi=O(x^3), phiFirst=O(x^2), phiSecond=O(x), with actual interval estimates, to the prior complete literal scalar theorem.')
span('D',8,'reviewed_actual_four_branch_geometry_and_exact_local_cone_audited',
     ['DEmbeddingObjective','DEmbeddingLocal','DEmbeddingCenter','DEmbeddingBounds'],
     'Literal branches/bStar, actual Frechet first/second derivatives and Hessians, global C2,1 bounds, compact sublevels, unique nonsmooth zero, original three-slab local cone including fourth-branch inactivity, half-height and exact center directional derivative -a_n^2.')
span('D',9,'reviewed_actual_infinite_embedded_search_and_uniform_localization_audited',
     ['SeedEmbeddingRun','SeedEmbeddingOracle','SeedEmbeddingSearch','DEmbeddingOracle','DEmbeddingRun',
      'DEmbeddingLocalization','DEmbeddingCenter','DEmbeddingBounds','DEmbeddingTarget','ReportEmbeddingEndToEnd'],
     'Every conditional transfer field is discharged from actual scalar plateaus and actual seed PointCertificates. Actual update invariance, recursive histories, accepted/trial gradients and values, phase formulas, all SPD matrices, strict decrease, derived point/value limits, starts and all queries uniformly approaching zero.')

modules['C'].update(
    status='principal_cluster_convergence_local_basin_and_all_pair_secant_verified_applications_pending',
    statement_review=review+'; audit/C_PRINCIPAL_VERIFICATION.md; audit/PLANAR_PRINCIPAL_PEER_REVIEW.md',
    remaining_claims='Finite-max nondegenerate application and positive branch-Hessian sufficient condition; semialgebraic alternative; explicit three-quadratic basin and RS exclusion; higher-dimensional partial construction and warning example. Stronger all-eligible-pair transversality/log-transport statements remain distinct from proved actual-run versions. Uniform all-pair secant and principal C theorem are now checked.')
span('C',2,'reviewed_principal_cluster_AC_convergence_and_local_basin_audited_finite_max_application_pending',
     ['PlanarSecantRun','PlanarConvergence','PlanarPrincipalEndToEnd'],
     'Literal compact-sublevel actual-run hypotheses, regularity only away from affine criticality, strict positive contours, actual affine-critical cluster. Affine correctness gives value and both norm conventions of solution distance, uniqueness gives iterate convergence. Source nondegenerate finite-max application remains separate.')
span('C',9,'reviewed_all_eligible_pair_secant_and_actual_tail_transport_audited_uniform_transport_pending',
     ['PlanarConvexCorner','PlanarBranchGeometry','PlanarPairControl','PlanarCrossingAlgebra',
      'PlanarCrossingSecant','PlanarCornerBounds','PlanarLocalSecant','PlanarCompactSecant','PlanarSecantField'],
     'One actual field; actual endpoint gradients, genuine tie point, exact jump cancellation and local convex C2 bounds. Weak Wolfe and inverse gradient-row control yield linear curvature and correction; all-pair constants/distance chosen uniformly by finite buffered cover. No finite crossing count or lower Hessian bound. Actual-run log transport is already checked; stronger all-pair log transport remains distinct.')
span('C',10,'reviewed_actual_full_BFGS_principal_contradiction_audited',
     ['PlanarSecantRun','PlanarConvergence','PlanarPrincipalEndToEnd'],
     'Combines derived positive limit and vanishing steps with actual support visibility, common field transport, secant correction and checked scalar-BFGS energy contradiction; no field, gradient alphabet, budget, iterate or matrix convergence premise.')
span('C',11,'reviewed_AC_and_local_basin_consequences_audited_nondegenerate_application_pending',
     ['PlanarConvergence','PlanarPrincipalEndToEnd'],
     'Objective-only local basin selected before all runs and arbitrary SPD/valid fixed line-search constants; full nondegenerate finite-max application still requires its local regular-branch reduction.')

modules['U'].update(
    status='principal_composite_theorems_and_all_literal_spike_examples_verified',
    statement_review=review+'; audit/NORMAL_SPIKE_VARIABLE_STATEMENT_REVIEW.md; audit/NORMAL_SPIKE_VARIABLE_PEER_REVIEW.md',
    remaining_claims='No remaining proof premise in the retained U principal/composite theorems or literal scalar, fixed-jump, rational-oracle and variable-jump examples. Final source/synthesis coverage review remains; nonsplitting explicitly requires c!=0, as documented in the correction ledger.')
span('U',14,'reviewed_actual_variable_jump_geometry_local_convergence_RS_failure_and_corrected_nonsplitting_audited',
     ['NormalSpikeVariableConvex','NormalSpikeVariableGradient','NormalSpikeVariableTangent',
      'NormalSpikeVariableGeometry','NormalSpikeVariableConvergence','NormalSpikeVariableNonsplit',
      'NormalSpikeVariableRadialBound','NormalSpikeVariableSamples','NormalSpikeVariableSeparation',
      'NormalSpikeVariableHessian','NormalSpikeVariableRadialHessian','NormalSpikeVariableTargets'],
     'Printed arbitrary-dimensional objective with norm(c)<1, actual strong convexity/unique zero/Hessians, local exceptional hyperplane and tangent map u+abs(v)c, objective-only local basin for all actual runs, fixed-band every-neighborhood RS failure. Nonsplitting for c!=0 holds for any differentiable smooth term and arbitrary scalar term without scalar regularity assumptions; c=0 remains allowed for convergence/separation.')

modules['L'].update(
    status='actual_quadratic_seed_geometry_verified_return_map_stable_orbit_and_embeddings_pending',
    statement_review=review+'; audit/L_QUADRATIC_SEED_STATEMENT_REVIEW.md; audit/L_QUADRATIC_SEED_PEER_REVIEW.md',
    remaining_claims='Actual five-dimensional return-map/positive-scale oracle neighborhood, derivative and certified spectrum, nonlinear stable-orbit existence/transversality, all actual infinite perturbed searches, C1,1 and countably affine local embeddings, identity initialization and literal Hessian bounds. Concrete Q_mu objective/minimizer/strong-convexity geometry is checked; the old homogeneous orbit is not assumed to persist.')
span('L',3,'reviewed_actual_quadratic_seed_minimizer_and_strong_convexity_audited',
     ['LQuadraticSeed','ReportEmbeddingEndToEnd'],
     'Every mu>0: exact Q_mu, muI actual branch Hessians, two explicit Euclidean strong-convexity conventions, coercivity/compact sublevels, gbar=(1,-16)/257 with exact least-norm hull proof, unique nonsmooth optimizer -gbar/mu and value -1/(514mu), exact active set{0,1}, actual origin subdifferential/nonstationarity. No perturbed-orbit assertion.')
for c in r['mathematical_corrections']:
    if c['id']=='C.negative_orientation_transport_sign':
        c['status']='corrected_algebra_actual_tail_transport_all_pair_secant_and_principal_theorem_verified'
    if c['id']=='U.variable_jump_nonadditivity_zero_parameter':
        c['status']='corrected_nonsplitting_for_nonzero_c_and_actual_variable_example_verified'
pairs=json.loads((ROOT/'audit/report_embedding_targets.json').read_text())
r['milestones']=[m for m in r['milestones'] if m['id']!='report_embedding_10']+[dict(
    id='report_embedding_10',status='verified',targets=[p[1] for p in pairs],audit='audit/STATUS.json',
    statement_review=review,explicit_theorems=len(status['verified_declarations']),
    audited_theorems=status['audited_declaration_count'],exact_targets=106)]
r['entire_report_verified']=False
path.write_text(json.dumps(r,indent=2)+'\n')
print('Tenth reviewed source register updated; entire report remains incomplete.')
