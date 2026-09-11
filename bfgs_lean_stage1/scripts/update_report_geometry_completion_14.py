#!/usr/bin/env python3
"""Publish fourteenth milestone source/status/documentation after its full gate."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_GEOMETRY_COMPLETION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_geometry_completion_source_hashes.json').read_text())
assert len(hashes)==582
for f,h in hashes.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text());mods={m['module']:m for m in r['modules']}
review='audit/REPORT_GEOMETRY_COMPLETION_STATEMENT_REVIEW.md'
def exports(files):
 out=[d['theorem'] for d in s['verified_declarations'] if any(d['source'].endswith('/'+f+'.lean') for f in files)]
 assert out,files
 return out
def span(tag,i,state,files,note):
 row=next(x for x in mods[tag]['coverage_spans'] if x['id']==f'{tag}.span.{i}')
 row.update(claim_review=state,review_note=note);row.pop('verification_note',None)
 if files:row['verified_exports']=sorted(set(row.get('verified_exports',[])+exports(files)))
mods['U'].update(status='verified_with_documented_nonzero_jump_parameter_correction',remaining_claims=[],statement_review='audit/RU_SOURCE_RECONCILIATION.md; audit/FIXED_NORMAL_PRINCIPAL_STATEMENT_REVIEW.md; audit/FIXED_NORMAL_COMPOSITE_STATEMENT_REVIEW.md')
span('U',1,'reviewed_preamble_not_a_mathematical_assertion',[],'TeX counters and scope only; original source read.')
span('U',5,'reviewed_common_proof_heading_not_a_separate_assertion',[],'Introduces already audited parallel/single-interface arguments; no additional premise or conclusion.')
mods['R'].update(status='recoverable_current_mathematics_verified_historical_four_piece_attribution_unresolved',statement_review='audit/RU_SOURCE_RECONCILIATION.md; audit/COERCIVE_SEED_INTERCEPT_CORRECTION.md',remaining_claims='The older four-piece numerical attribution lacks a recoverable objective. Its literal historical numbers are not verified; actual current D optimizer/intercept correction is proved. All recoverable current theorem/family/boundary claims and source setup are audited.')
span('R',1,'reviewed_preamble_not_a_mathematical_assertion',[],'TeX setup and counters only.')
span('R',2,'reviewed_literal_RS_endpoint_definitions_compact_support_bounds_and_4GR_estimate_audited',['RadialCertificate','RadialEquivalence','ConvexAnalysis','EuclideanEstimates'],'Actual base derivative supporting error, two-error curvature identity, literal4GR Euclidean bound, compact bound for every actual supporting vector and exact ordered-positive-band RS definition. Infinite admissible full-BFGS model and stated all-ray limitation match source.')
span('R',9,'reviewed_named_family_scope_qualification',[],'Heading and explicit minimizer/compact-basin qualifications inherited by the audited family theorems.')
span('R',14,'reviewed_boundary_section_heading',[],'Heading only; mathematical boundaries are audited in the next two spans.')
mods['L'].update(status='verified_with_documented_Jacobian_rounding_correction',remaining_claims=[],
 statement_review=review+'; audit/L_SOURCE_MAP.md; audit/L_SHAPE_PRECISION_STATEMENT_REVIEW.md; audit/L_SHAPE_PRECISION_PEER_REVIEW.md')
span('L',5,'reviewed_actual_spectrum_inverse_invariant_manifold_and_Jacobian_precision_audited',
 ['LShapeFineCertificate','LShapePrecision'],
 'Kernel interval proofs certify actual derivative entries at twenty-decimal precision; all original displayed entries have error<1e-15. The lower-left nearest15 rounding must end427498 rather than427499. The unchanged original source and exact numerical correction are documented. Complete368-line/50-group source map closes all retained L claims, preserving the expressly unclaimed globallyC2/lower-curvature combination.')
mods['C'].update(status='principal_uniform_endpoint_and_arbitrary_dimensional_constant_rank_theorems_verified_semialgebraic_alternative_pending',
 statement_review=review+'; audit/C_CONSTANT_RANK_STATEMENT_REVIEW.md; audit/C_CONSTANT_RANK_INDEPENDENT_PEER_REVIEW.md',
 remaining_claims='Only the A-dependent semialgebraic alternative remains mathematically open. Actual arbitrary-dimensional constant-rank C1 common-rate field and uniform all-pair secant correction are now derived; C2 input guarantees C1 rather than C-infinity regularity. General projected transport/convergence in higher dimension remains expressly unclaimed.')
span('C',15,'reviewed_constant_rank_C1_field_secant_and_actual_spatial_transport_warning_audited',
 ['ConstantRankTargets','ConstantRankLocalField','OriginalActiveRateChart','RatePatchSecant','AffineIndependentRank'],
 'Actual fixed-original-active gradient-difference rank, derived persistent affine basis and canonical minimum-norm point, one buffered finite C1 field, visibility against every actual subgradient and uniform actual Euclidean all-pair secant bound. Affine-independence sufficiency proved. C2-to-C1 regularity qualification recorded; no matrix/iterate/transport premise. Previously checked actual three-dimensional warning and radial convergence retained.')
mods['A'].update(status='actual_affine_geometry_and_arbitrary_degree_polynomial_infrastructure_verified_general_elimination_and_path_closure_pending',
 statement_review=review+'; audit/A_POLYNOMIAL_MULTIPLICITY_VERIFICATION.md; audit/A_QUADRATIC_PROJECTION_VERIFICATION.md; audit/A_POLYNOMIAL_PSEUDODIVISION_VERIFICATION.md',
 remaining_claims='General nonlinear Boolean polynomial projection/quantifier elimination, finite semialgebraic piecewise-C1 path decomposition, and actual support/affine-critical definability/finite-value application. Degree/multiplicity strata, nonzero-fiber derivative charts, exact global single-quadratic-atom projections and arbitrary-degree positive pseudo-division are verified infrastructure, not the general theorem.')
span('A',4,'reviewed_polynomial_strata_local_charts_quadratic_projection_pseudodivision_general_closure_pending',
 ['PolynomialMultiplicityTargets','QuadraticProjectionTargets','PseudoDivisionTargets'],
 'Actual finite degree/multiplicity strata and derivative charts, global quadratic existential/universal sign and root projection with all degeneracies, and one finite family of degree-decreasing positive-scaled root-sign remainders chosen before every specialization. No general Boolean projection or finite smooth-path theorem is inferred from these fragments.')
mods['H']['remaining_claims']=[
 'The earlier exact three-gradient rank-two cardinality-sharpness cross-reference awaits its separately reviewed source wrapper central release.',
 'Recurrent rank at least three zero-value iterate behavior is expressly open, not an asserted theorem.']
mods['H']['statement_review']=review+'; audit/TWO_PIECE_TERMINATION_STATEMENT_REVIEW.md; audit/TWO_PIECE_TERMINATION_INDEPENDENT_REVIEW.md'
span('H',14,'reviewed_two_piece_finite_termination_and_general_linear_image_no_infinite_run_cardinality_crossref_pending',
 ['TwoPieceTermination','TwoPieceRay','TwoPieceProjection','TwoPieceTargets'],
 'For literal|u|+t, actual finite full-BFGS transition relation is well-founded and every initial differentiable SPD state reaches an actual terminal state whose actual search direction tends to minus infinity. Arbitrary finite-dimensional full-row-rank linear images have no infinite actual admissible continuation. Published two-piece result retains attribution; no finite-termination result for general many-piece objectives. Concrete three-gradient rank-two cardinality-sharpness central wrapper remains separately pending.')
corrections=[
 dict(id='C.constant_rank_field_regularity',source='C.tex388-406',status='actual_C1_construction_and_uniform_secant_bound_verified',correction='C2 branches guarantee a C1 gradient family and C1 common-rate field. The source word smooth is qualified accordingly; no C-infinity regularity or higher-dimensional projected transport is inferred.',review='audit/C_CONSTANT_RANK_STATEMENT_REVIEW.md'),
 dict(id='L.Jacobian_lower_left_nearest_rounding',source='L.tex168-174',status='actual_Jacobian_precision_and_rounding_correction_verified',correction='All four printed approximate entries have error<1e-15, but the lower-left nearest15-decimal rounding is0.751501570427498, not0.751501570427499. Actual derivatives are enclosed within5e-21 of twenty-decimal centers; original source unchanged.',review='audit/L_SHAPE_PRECISION_STATEMENT_REVIEW.md')]
for c in corrections:
 assert not any(x['id']==c['id'] for x in r['mathematical_corrections'])
 r['mathematical_corrections'].append(c)
pairs=json.loads((ROOT/'audit/report_geometry_completion_targets.json').read_text())
assert len(pairs)==16
r['milestones'].append(dict(id='report_geometry_completion_14',status='verified',targets=[x[1] for x in pairs],
 audit='audit/STATUS.json',statement_review=review,explicit_theorems=len(s['verified_declarations']),
 audited_theorems=s['audited_declaration_count'],exact_targets=178,
 conditional_infrastructure=['Single-quadratic-atom projection is not general Boolean elimination','Positive pseudo-division and multiplicity charts are infrastructure, not path decomposition','Two-piece arbitrary-dimensional target is no infinite continuation; detailed terminal-ray target is literal two-dimensional model']))
r['entire_report_verified']=False;p.write_text(json.dumps(r,indent=2)+'\n')
e=len(s['verified_declarations']);a=s['audited_declaration_count']
marker='## Fourteenth milestone: constant-rank geometry, precision and two-piece termination'
text=f'''\n\n{marker}\n\nThe frozen pinned build and full transitive audit passed {e:,} explicit theorems,\n{a:,} total theorem declarations,178 exact targets and582 frozen Lean files.\nOnly propext,Classical.choice and Quot.sound occur. Evidence is in\naudit/report_geometry_completion_check.log and the accompanying frozen manifest,\ncompiler logs, declaration inventory and source statement review.\n\nC's actual arbitrary-dimensional constant-rank construction now derives one C1\ncomparison field and uniform all-endpoint secant correction from the original\nactive gradients. C2 input does not justify C-infinity field regularity; the\nqualification is explicit. L's complete source map and actual Jacobian precision\ncertificate close its remaining display claim, with a documented last-digit\nnearest-rounding correction. The literal two-piece actual BFGS transition relation\nis well-founded, and its terminal search ray exposes unboundedness. Arbitrary\nfull-row-rank linear images have no infinite actual admissible continuation.\nThe pre-existing two-piece theorem retains Xie–Wächter attribution.\n\nA now has actual finite degree/multiplicity strata, derivative charts, exact\nglobal quadratic root/sign projection with degeneracies, and arbitrary-degree\npositive pseudo-division with one finite remainder family chosen before every\nspecialization. These fragments do not establish general Boolean projection.\nGeneral semialgebraic elimination and finite smooth paths, the dependent C\nalternative, D numerical-display precision and final synthesis/evidence\nreconciliation remain active. The entire report is not yet verified.\n'''
for name in ['ENTIRE_REPORT_PLAN.md','MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md']:
 p=ROOT/name;old=p.read_text();assert marker not in old;p.write_text(old+text)
p=ROOT/'README.md';old=p.read_text();old=old.replace('all 4,291 explicit\ntheorems and 6,264 theorem declarations including generated auxiliaries. All 162',f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 178')
old=old.replace('audit/report_source_closure_check.log','audit/report_geometry_completion_check.log',1)
old=old.replace("A's general semialgebraic closure, C's higher-dimensional partial field/secant\nassertion and A-dependent alternative, and final source/evidence reconciliation\nremain open.",'''The fourteenth tranche verifies C's actual arbitrary-dimensional constant-rank\nC1 field/secant theorem, L's Jacobian precision and complete source reconciliation,\nactual two-piece termination and the separate arbitrary-dimensional no-infinite-run\nresult, and further polynomial elimination infrastructure. See\n[audit/REPORT_GEOMETRY_COMPLETION_STATEMENT_REVIEW.md](audit/REPORT_GEOMETRY_COMPLETION_STATEMENT_REVIEW.md).\nA's general semialgebraic closure, its dependent C alternative, D's remaining\ndisplay precision, and final source/synthesis/evidence reconciliation remain open.''')
p.write_text(old)
for tag,state in [('U','verified with the documented nonzero-jump-parameter correction'),('R','recoverable current mathematics verified; historical four-piece attribution remains unresolved')]:
 p=ROOT/f'audit/module_{tag}_inventory.md';old=p.read_text()
 assert not old.startswith('Current source reconciliation'),tag
 p.write_text(f'Current source reconciliation at milestone14: **{state}**.\nSee [RU_SOURCE_RECONCILIATION.md](RU_SOURCE_RECONCILIATION.md) and REPORT_STATUS.json.\nChronological pending entries below are historical, not current status.\n\n'+old)
print(f'Fourteenth register/docs updated: {e} explicit/{a} total/178 exact targets; entire report incomplete.')
