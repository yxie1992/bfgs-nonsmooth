#!/usr/bin/env python3
"""Static source/statement reconciliation; this is not a replacement Lean audit."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
SOURCE = PROJECT.parent / 'BFGS_MASTER_REPORT_LaTeX/report/chapters/L.tex'
rows = []

def row(a, b, claim, refs='', note='', status='covered'):
    rows.append(dict(first=a,last=b,claim=claim,status=status,
        references=[r.split(':') for r in refs.split(';') if r],note=note))

row(1,16,'LaTeX notation and counters',status='scaffolding')
row(17,28,'Ordinary full inverse BFGS; unit-first midpoint/doubling search; c1=1/10000,c2=1/2; differentiable actual queries and strict decisions',
    'DeterministicLineSearch:search;DeterministicLineSearch:fromMetric;LGlobalTargets:globalFailure;LIdentityGeometry:smoothLocalFailure;LIdentityGeometry:stepLocalFailure',
    'The fuel-5 success equalities prove termination within the exact displayed history. Fuel is a proof representation of a finite successful execution, not an algorithm modification. Strict inequalities exclude equality-convention dependence.')
row(29,38,'L:thm:global: literal three slopes, every mu>0, strong convexity/coercivity/unique nonsmooth minimizer, global branch Hessian mu I, actual small bad runs and repeating lengths',
    'ReportEmbeddingTargets:QuadraticSeedTarget;ReportEmbeddingEndToEnd:quadraticSeed;LGlobalTargets:GlobalFailureTarget;LGlobalTargets:globalFailure',
    'Geometry and dynamics are separate exact exports for the same literal objective. The global target quantifies the physical neighborhood before choosing an actual run.')
row(39,48,'L:thm:local: one objective and one identity initialization for an infinite family of bad starts, both four-C1,1 and countable-polyhedral versions',
    'LIdentityGeometry:SmoothLocalFailureTarget;LIdentityGeometry:smoothLocalFailure;LIdentityGeometry:StepLocalFailureTarget;LIdentityGeometry:stepLocalFailure',
    'Each target combines the objective geometry, actual Hessian property, exact full-search family, starts and centers tending to zero, and whole-query locality. Constants/objective/coordinate matrix do not vary with the start index.')
row(49,58,'Explicitly unclaimed stronger local counterexample with four globally C2 branches; subsequent counters',
    note='Source line 49 explicitly leaves this stronger combination unproved. It is not an unverified assertion of Module L and must not be silently added to its conclusion.',status='not_claimed')
row(59,60,'Inherited exact algebraic seed and nine strict query decisions',
    'AlgebraicSeedRoot:exact_closed_box;AlgebraicSeedCycle:source_cycle;AlgebraicSeedDeterministicTrace:actual_deterministic_seed_failure',
    'The mathematical facts are kernel-checked. The historical external verifier citation is provenance, not a premise; correspondence to an external program is not asserted by these Lean declarations.')
row(61,72,'Literal slopes, six source polynomials and both defining root equations',
    'AlgebraicSeedCycle:g0;AlgebraicSeedCycle:g1;AlgebraicSeedCycle:g2;AlgebraicSeedData:P;AlgebraicSeedRoot:exact_closed_box')
row(73,78,'Existence and uniqueness in the printed rational radius-10^-30 sup-norm box',
    'AlgebraicSeedData:center;AlgebraicSeedData:radius;AlgebraicSeedRoot:exists_unique_root;AlgebraicSeedRoot:exact_closed_box',
    'The rational center digits are exact definition data. The contracting-map proof checks actual polynomial coefficients and maps the actual closed box into itself.')
row(79,83,'Literal rho and initial-point formula; rho in (0.060,0.061)',
    'AlgebraicSeedRoot:ratio;AlgebraicSeedOrbitData:initialPoint;AlgebraicSeedOracleData:tight_ratio;AlgebraicSeedOrbitData:root_tight_box')
row(84,89,'Exact three full-BFGS steps, M1, M3=rho I, z3=rho z0, unique accepted active branches',
    'AlgebraicSeedCycle:first_update;AlgebraicSeedCycle:source_cycle;AlgebraicSeedOrbitGeometry:source_phase_two_step;AlgebraicSeedOrbitGeometry:source_metric_two_update;AlgebraicSeedOrbitData:StrictActive',
    'Actual source point/trial certificates instantiate StrictActive; they are not assumed active gradients.')
row(90,95,'Exact finite lists, rejected values rise, accepted decrease ratio>1/3, new/old directional ratio<0, persistence of strict decisions',
    'AlgebraicSeedOrbitData:TrialCertificate;AlgebraicSeedDeterministicTrace:trialHistory;LNormalizedOracle:seed_accept_margins;LNormalizedOracle:seed_reject_margin;LNormalizedOracle:conditions_eventually',
    'TrialCertificate uses equivalent denominator-safe inequalities: negative old directional product, accepted 1/3 decrease inequality, positive new product, and strict rejection value rise. Dividing gives the printed ratios.')
row(96,106,'Downhill separator, least-norm gbar, exact unique minimizer/value, exactly two active branches there, actual origin subdifferential',
    'AlgebraicSeedFailure:source_downhill_pairings;LQuadraticSeed:gbar_least_norm;LQuadraticSeed:gbar_unique_least_sqNorm;ReportEmbeddingTargets:QuadraticSeedTarget;ReportEmbeddingEndToEnd:quadraticSeed')
row(107,115,'LaTeX section counters',status='scaffolding')
row(116,128,'Five normalized coordinates, physical x=tau z,H=tau M, boundary seed; fixed input tau during three substeps',
    'LNormalizedReturn:State;LNormalizedReturn:shape;LNormalizedReturn:seed;LNormalizedReturn:internal;LNormalizedOracle:physicalPoint;LNormalizedOracle:physicalMetric',
    'The perturbed orbit is independently constructed; the original homogeneous exact orbit is not asserted to remain unchanged.')
row(129,141,'Literal formal gradients, steps, secants, full update and normalization return map',
    'LNormalizedReturn:currentGradient;LNormalizedReturn:step;LNormalizedReturn:secant;LNormalizedReturn:substep;LNormalizedReturn:returnMap;LNormalizedReturn:physical_update')
row(142,142,'Nonzero actual denominators, return factor rho>0, analyticity on an open boundary neighborhood allowing negative tau',
    'LNormalizedReturn:seed_denominator_positive;LNormalizedReturn:seed_returnFactor;LNormalizedReturn:regular_analytic_neighborhood')
row(143,146,'L:lem:agreement: actual implementation has exactly the certified histories and physical return map throughout a positive-scale neighborhood',
    'LNormalizedOracle:actual_implementation_neighborhood',
    'This theorem gives actual derivatives, SPD metrics, update equalities, complete histories, and physical normalization identities. It holds for all real mu, with the source c1/c2 as a valid specialization.')
row(147,153,'Normalized value/gradient formula and continuity of all strict branch/search tests; no reset',
    'LNormalizedOracle:physical_value_of_active;LNormalizedReturn:physical_branch_gradient;LNormalizedOracle:continuous_armijoMargin_seed;LNormalizedOracle:continuous_wolfeMargin_seed;LNormalizedOracle:oracle_neighborhood;LNormalizedOracle:Conditions.actual_matrix_update')
row(154,162,'LaTeX section counters',status='scaffolding')
row(163,167,'Boundary shape map independent of physical point coordinates and mu; actual shape derivative',
    'LNormalizedReturn:internal_boundary_translate;LShapeDerivative:shapeMap;LShapeMapDifferentiability:shapeMap_hasFDerivAt;LShapeSpectrum:actual_middle_block')
row(168,174,'Printed approximately 15-digit Jacobian entry displays',
    'LShapeSpectrum:source_jacobian_bounds;LShapePrecision:actualJacobianPrecision',
    'CLOSED IN MAIN SCOPED AUDIT: LShapePrecision.actualJacobianPrecision proves actual entries within5e-21 of four twenty-decimal centers and all original displays within1e-15. The original lower-left entry is above the actual value by more than0.5e-15, so nearest15 rounding should end ...427498. See L_SHAPE_PRECISION_STATEMENT_REVIEW.md; 2 files/16 declarations/1 exact target passed delivered-only main compiler/type/axiom audit and independent review. Central whole-project release integration remains separate.',status='covered_main_scoped')
row(175,180,'Exact characteristic signs throughout the root box and both distinct real eigenvalue intervals',
    'LShapeIntervalCertificate:jacobian_bounds;LShapeSpectrum:box_of_original_ball;LShapeSpectralAlgebra:signs_of_entry_bounds;LShapeSpectrum:source_characteristic_signs;LShapeSpectrum:source_shape_roots',
    'The generic interval theorem is valid on a larger rational box. Combining it with box_of_original_ball and the generic sign theorem proves the source whole-box assertion; the source-root wrappers instantiate it. No floating-point eigensolver is a dependency.')
row(181,191,'Actual full block Jacobian, fixed finite C/a/b, exact mu scaling of the scale column',
    'LReturnParameterBlock:Cleft;LReturnParameterBlock:Cright;LReturnParameterBlock:upperScale;LReturnParameterBlock:middleScale;LReturnParameterBlock:actual_parameter_block;LNormalizedReturn:return_derivative_point_columns;LNormalizedReturn:return_derivative_last_row')
row(192,197,'Full spectrum with multiplicities, no zero/unit-circle roots, exactly two stable directions, local smooth inverse',
    'LGlobalTargets:spectrum;LGlobalTargets:localInverse;LReturnStableGraph:source_splitting',
    'Exact diagonalization has two contracting and three expanding coordinates. Spectrum/no-zero/no-unit-circle conclusions are direct consequences of its displayed rational root intervals and positive rho bounds.')
row(198,199,'Rho eigenvector with scale coordinate one; stable space transverse to tau=0',
    'LBlockEigen:scale_eigen;LReturnStableGraph:source_splitting;LReturnStableGraph:source_smooth_stable_graph',
    'The actual coordinate equivalence satisfies (E z)_4=z.stable_1. This is a stronger concrete transversality identity.')
row(200,203,'Actual smooth embedded two-dimensional local stable manifold, actual stable tangent space, arbitrarily small positive scales',
    'LStableManifoldTargets:lStableManifold;LStableInvariantManifold:lStableInvariantManifold',
    'The final stronger target also asserts local forward invariance on the SAME graph. Actual analytic bounded-sequence lifting and an implicit-function argument construct the chart; no smooth orbit selection or abstract manifold existence is assumed.')
row(204,209,'Positive scale invariant, SPD phase metrics, actual full-BFGS trajectories and physical x,H tending to zero',
    'LPositiveOrbit:positive_orbit_of_splitting;LNormalizedReturn:internal_posDef_of_regular;LNormalizedOracle:Conditions.physicalMetric_posDef;LGlobalTargets:globalFailure',
    'The final global run theorem discharges the generic splitting/orbit hypotheses using the actual derivative and actual oracle. Matrix convergence is a proved feature of this counterexample, not an assumption used to prove general BFGS convergence.')
row(210,214,'All intermediate/rejected queries converge, strict decisions persist, values decrease to zero, nonstationarity, arbitrary whole-query locality, no numerical shooting claim',
    'LGlobalTargets:GlobalFailureTarget;LGlobalTargets:globalFailure',
    'The query limit is quantified over every phase-matching choice of actual query. Neighborhood-before-run quantifiers give whole-orbit locality. The source numerical-shooting warning is not a separate mathematical premise.')
row(215,223,'LaTeX section counters',status='scaffolding')
row(224,233,'Literal mu, center, slopes, parameters, scale r=1/128; exact b0=b1=1791/1024 and 1.7<bi<34',
    'LEmbeddingObjective:mu;LEmbeddingObjective:center;LEmbeddingObjective:slope;LEmbeddingObjective:parameter;LEmbeddingObjective:parameter_first;LEmbeddingObjective:parameter_second;LEmbeddingObjective:parameter_bounds;LScalarGeometric:theta;LScalarGeometric:scale')
row(234,237,'Exactly two parameter values, literal theta_b and epsilon',
    'LEmbeddingObjective:parameter_first;LEmbeddingObjective:parameter_second;LEmbeddingGradientBounds:parameter_third_gt;LScalarRamp:center;LScalarRamp:epsilon',
    'Exactly two values follows immediately from b0=b1=1791/1024<33<b2 and the three-element index. No pruning or distinctness assumption is needed.',status='elementary_consequence')
row(238,245,'Monotone cubic C1 ramp, actual integral primitive, exact area, derivative range 0..768',
    'LScalarRamp:ramp_eq_zero;LScalarRamp:ramp_eq_one;LScalarRamp:ramp_eq_cubic;LScalarRamp:ramp_monotone;LScalarRamp:ramp_contDiff;LScalarTargets:lScalarRamp')
row(246,252,'Literal scalar interval formula and exact zero, negative quadratic and outer affine extensions',
    'LScalarTargets:LScalarDefinitionTarget;LScalarTargets:lScalarDefinition',
    'The implementation is an actual convergent series; the interval theorem proves equality to the printed piecewise formula, including shared endpoints.')
row(253,264,'L:lem:scalar: convex/nonnegative/coercive/unique zero, global C1,1, C2 off zero, not twice differentiable at zero, exact nodes/closed plateaus and 768/b curvature bound',
    'LScalarTargets:lScalarRegularity;LScalarTargets:lScalarNodes;LScalarTargets:lScalarPeaks',
    'Actual derivative existence is asserted with HasDerivAt, not merely a value of Lean total deriv. The results hold on the larger closed parameter interval [1.7,34].')
row(265,272,'Positive interval first/second derivatives, matching identity, derivatives at zero, O(x)/O(x^2), global Lipschitz assembly',
    'LScalarJets:positiveSlope_interval;LScalarCurvature:positiveCurvature_interval;LScalarRamp:matching_identity;LScalarSmallBounds:positive_asymptotic_orders;LScalarRegularity:phi_second_hasDerivAt_pos;LScalarTargets:lScalarRegularity')
row(273,280,'Both normalized plateau lengths>1/2 and two derivative/x limits ruling out second derivative at zero',
    'LScalarRamp:lowerLength_formula;LScalarRamp:upperLength_formula;LScalarRamp:plateau_lengths;LScalarRegularity:derivative_ratio_on_nodes;LScalarRegularity:derivative_ratio_on_shifted_nodes;LScalarRegularity:phi_not_twice_differentiable_zero')
row(281,287,'Literal four-branch maximum, global mu strong convexity, actual Euclidean gradient Lipschitz constant512 and sharper439/446/27 bounds, fourth Hessian mu I',
    'LEmbeddingGeometryTargets:regularity;LEmbeddingGradientBounds:gradientBound_source;LEmbeddingSourceDetails:branch_last_hessian',
    'Gradient bounds are written as exact sum-of-squares inequalities in the Euclidean geometry, not the default coordinate supremum norm.')
row(288,293,'Quadratic lower bound, compact sublevels/unique zero, branch gradients and actual directional derivative max(0,h2), nonsmooth minimizer',
    'LEmbeddingGeometryTargets:origin;LEmbeddingGeometry:branch_ray_hasDerivAt_zero;LEmbeddingGeometry:objective_directional_derivative_zero')
row(294,300,'Actual finite-max active-gradient agreement/Taylor bound and classical Hessian mu..512 without a globally Lipschitz full-max gradient',
    'LEmbeddingGeometryTargets:HessianTarget;LEmbeddingGeometryTargets:hessian',
    'Twice differentiable means the first Frechet derivative exists on a neighborhood and its field is Frechet differentiable at the point. The target explicitly records this conventional iterated-derivative domain condition. It does not assert a second-order directional or Peano derivative result.')
row(301,309,'LaTeX section counters',status='scaffolding')
row(310,316,'Literal centers/offset and exact old-branch copy identity under the closed half-dot bound',
    'LEmbeddingLocal:copyCenter;LEmbeddingLocal:copyPoint;LEmbeddingLocal:offset;LEmbeddingLocal:scalar_copy;LEmbeddingLocal:branch_copy')
row(317,320,'Fourth branch inactive and exact whole-objective local model on one fixed open domain',
    'LEmbeddingLocal:last_residual_copy_negative;LEmbeddingLocal:local_model;LEmbeddingGeometryTargets:localModel',
    'Proved for all natural scales, including n=0; this strengthens the source n>=1 range.')
row(321,329,'Choose one actual small Q orbit, transfer all gradients/steps/matrices/queries exactly at every scale, one shared initial SPD metric',
    'LSeedCopies:run;LActualCopies:smoothData;LActualCopies:stepData;LActualCopies:point_formula;LActualCopies:matrix_formula;LActualCopies:gradient_formula;LActualCopies:actual_search',
    'The final instantiated smoothData/stepData use their proved objective identities. Generic ScaledCopy hypotheses are discharged, not final assumptions.')
row(330,334,'Every copied run converges to its center and its values decrease to the exact positive a_n^2 offset',
    'LActualCopies:point_limit;LActualCopies:value_limit;LActualCopies:values_above_limit;LActualCopyTargets:smoothFailure;LActualCopyTargets:stepFailure')
row(335,339,'Actual nonstationary centers, starts to zero, uniform whole-query norm locality, one fixed metric',
    'LActualCopies:centers_nonstationary;LActualCopies:starts_tendsto;LActualCopies:matrix_formula;LActualCopyLocality:trial_norm_bound;LActualCopyLocality:uniform_locality',
    'The exported uniform bound is a_n*(||center||_infinity+1), using a source orbit chosen in the coordinate unit ball. It proves the exact all-neighborhood locality in the target. The literal Euclidean triangle bound with the supremum of seed-query Euclidean norms is an elementary consequence of the exact query identity and norm_add_le; that particular supremum expression is not a separate named export. Center nonstationarity is proved directly from positive center value and the zero global minimum, so no unsupported subdifferential identity is used.')
row(340,347,'One actual SPD square root whitens all starts to H0=I, all searches preserved, fixed positive lambda-min/max constants, transformed whole-family limits',
    'LWhiteningGeometry:coordinateMatrix;LWhiteningGeometry:coordinateMatrix_square;LWhiteningGeometry:lowerConstant;LWhiteningGeometry:upperConstant;LIdentityTargets:smoothIdentityFailure;LIdentityGeometry:smoothLocalFailure',
    'The coordinate matrix is chosen once from the single source run H0, independently of the scale index. The square root/eigenvalue bounds, full-update covariance and actual derivative/search covariance were separately peer-reviewed.')
row(348,356,'LaTeX section counters',status='scaffolding')
row(357,359,'Strict-step ramp and hinge primitive, exact actual countably affine scalar, same nodes/closed plateaus and same actual copy family',
    'LScalarStepTargets:lScalarStepDefinition;LScalarStepTargets:lScalarStepGeometry;LScalarStepTargets:lScalarStepNodes;LScalarStepTargets:lScalarStepLocal;LActualCopyTargets:stepFailure')
row(360,365,'Independent q0/q1, zero arguments inactive away from origin, actual local finite polyhedrality/affine germs, Hessian mu I; after whitening fixed SPD mu H0',
    'LStepEmbeddingTargets:lStepEmbeddingPolyhedral;LIdentityGeometry:fixedHessian;LIdentityGeometry:step_decomposition;LIdentityGeometry:step_actual_hessian_bounds;LIdentityGeometry:stepLocalFailure',
    'The actual Hessian existence and fixed value are proved already at every differentiability point. The target retains a countable attained affine maximum; it does not label these scalar branches smooth.')
row(366,368,'Closing whitespace and LaTeX group',status='scaffolding')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

seen=[]
refs={}
for r in rows:
    seen.extend(range(r['first'],r['last']+1))
    for module,name in r['references']:
        p=PROJECT/'BfgsVerification'/f'{module}.lean'
        assert p.is_file(),str(p)
        # This validates only named source correspondence, not elaboration or axioms.
        assert re.search(r'^(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|abbrev|structure)\s+'
                         +re.escape(name)+r'(?=\s|\{|\(|:)',p.read_text(),re.M),(module,name)
        refs[str(p.relative_to(PROJECT))]=digest(p)
assert seen==list(range(1,len(SOURCE.read_text().splitlines())+1)), 'incomplete/overlapping line partition'
data={'source':str(SOURCE.relative_to(PROJECT.parent)),'source_sha256':digest(SOURCE),
      'kind':'read-only mathematical/source statement reconciliation; not a new Lean audit',
      'release_note':'Main geometry/orbit/manifold targets released in milestone13; main precision scoped audit completed subsequently; next whole-project audit is root-owned',
      'rows':rows,'referenced_main_hashes':refs,
      'precision_scoped_hashes':json.loads((HERE/'l_shape_precision_source_hashes.json').read_text()),
      'precision_scoped_validation':(HERE/'l_shape_precision_validation.log').read_text()}
(HERE/'l_source_map.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
head='''# Complete Module L source reconciliation

This review partitions every line of the unchanged `report/chapters/L.tex` and maps its mathematical assertions to the actual final main definitions and theorems. It does not rerun or replace the successful scoped compiler/axiom audits. The main geometry, orbit and stable-manifold targets were released in milestone13. The additional main precision proof has passed its delivered-only scoped audit and independent review; the next central release audit remains root-owned.

The principal mathematical theorem/lemma chain is covered: `L:thm:global`, both versions of `L:thm:local` with one fixed identity initialization, `L:lem:agreement`, and `L:lem:scalar`. The ancillary smooth two-dimensional stable-manifold assertion now includes an actual embedded chart, actual stable tangent-space equality, actual convergent orbits, and local invariance on that same chart. No additional convergence, matrix, orbit, active-gradient, or differentiability assumption is hidden in the final source targets.

The formerly remaining numerical-display precision item at lines168–174 is now closed in a separately scoped, compiler/type/axiom-audited main proof (two files, sixteen declarations, one exact target). It proves all original printed entries have error<10^-15 and supplies twenty-decimal centers with error<=5e-21. It also proves a nearest-rounding correction in the last digit of the lower-left entry: ...427498. The actual main precision sources and self-contained audit evidence are delivered; incorporation into the next central whole-project release remains pending. The original research source is preserved.

`covered` means actual checked declarations/definitions establish the claim, sometimes as a direct specialization or elementary combination described in the note. `elementary_consequence` identifies simple source bookkeeping not packaged in its own named wrapper. `covered_main_scoped` identifies the subsequently delivered main precision scope, whose scoped audit passed but whose next central release integration is separate. `not_claimed` is a stronger statement expressly withheld by the source. Empty lines, section headings and counters are included to make the coverage partition complete.

| Source lines | Assertion | Status | Actual main declarations | Review notes |
| --- | --- | --- | --- | --- |
'''
body=[]
for r in rows:
    refsmd='; '.join(f'`{m}.{n}`' for m,n in r['references']) or '—'
    body.append(f"| {r['first']}–{r['last']} | {r['claim']} | {r['status']} | {refsmd} | {r['note']} |")
foot='''

## Final contracts and scope distinctions

- Global geometry: `BfgsVerification.LQuadraticSeed.quadraticSeed : QuadraticSeedTarget`, in `ReportEmbeddingEndToEnd.lean`; actual arbitrary-mu bad runs: `BfgsVerification.LGlobalTargets.globalFailure : GlobalFailureTarget`.
- Both final local source conclusions: `BfgsVerification.LWhitening.smoothLocalFailure : SmoothLocalFailureTarget` and `BfgsVerification.LWhitening.stepLocalFailure : StepLocalFailureTarget`, in `LIdentityGeometry.lean`.
- Actual spectrum/local inverse: `LGlobalTargets.spectrum` and `LGlobalTargets.localInverse`. The exact mu-dependent block formula is independently exported as `LReturnParameterBlock.actual_parameter_block`.
- Final ancillary manifold source conclusion: `BfgsVerification.LReturnStableGraph.lStableInvariantManifold : LStableInvariantManifoldTarget`, in `LStableInvariantManifold.lean`. The weaker predecessor `lStableManifold` remains available.
- The four-smooth-branch local objective is globally C1,1, not globally C2. The stronger globally C2 claim at source line49 is explicitly not claimed. The step alternative has an actual fixed Hessian at every differentiability point but an actual nonsmooth countable-affine residual.
- All curvature/smoothness constants are expressed using the actual Euclidean quadratic form. The coordinate supremum norm is used where appropriate for root boxes and a convenient uniform-locality estimate; finite-dimensional topologies agree. The exact Euclidean supremum-query triangle inequality is a direct consequence of the actual copied query identity, not a new unproved geometric assumption.
- The final classical-Hessian target explicitly states existence of the first Frechet derivative nearby and differentiability of that derivative field at the point. It is not a statement about an isolated second-order directional or Peano expansion.
- The original report is preserved. No mathematical correction to a principal L conclusion was identified. The last-digit precision item is now proved in the delivered main scope above; incorporating it into a subsequent central whole-project release remains the outstanding release step. Historical program/prose provenance is distinguished from the new kernel proof evidence.

## Reconciliation validation

`python3 audit/generate_l_source_map.py` checks that the rows form a non-overlapping complete partition of source lines1–368 and that every cited declaration is present in its named main file. It records the unchanged source hash and hashes of the referenced main files in `l_source_map.json`. This static check is explicitly not a compiler, theorem-type, transitive-axiom or correctness check; those existing evidence streams remain authoritative.
'''
(HERE/'L_SOURCE_MAP.md').write_text(head+'\n'.join(body)+foot)
print(f'PASS static reconciliation: {len(rows)} line groups, all {len(seen)} source lines, {len(refs)} referenced main files; source {digest(SOURCE)}')
