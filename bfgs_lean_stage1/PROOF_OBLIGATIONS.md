# Module M source-to-proof register

**All 14 registered Module M targets are proved, compiled, and axiom-audited.**
See `audit/STATUS.json` for the actual run and declaration inventory. The original
draft targets in `Definitions.lean` have not been altered.

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/foundation.tex`, preserved also
as `reference/foundation.tex`. No original research source was edited.

## 1. Actual matrix hierarchy — complete

For SPD H, alpha>0, q=gᵀHg>0 and beta=−yᵀHg/q>0, the checked theorem proves

    e_j(inverseBFGS(H,−alpha H g,y))
      <= ||y||²/(beta² q) e_(j+1)(H) + (alpha/beta)e_j(H)

for 1<=j<=n and arbitrary n. `e_j` is the original `principalSum`: a sum of actual
principal submatrix determinants.

| Original obligation | Checked implementation |
|---|---|
| M1.1 SPD/invertible compression | `metricGram_posDef`, `metricGram_posSemidef` |
| M1.2 Actual inverse-BFGS projected/rank-one form | `inverseBFGS_projection_form`; actual compressed form in `BFGSCompression.lean` |
| M1.3 Rank-two determinant identity | `CompressionDeterminant.det_rank_two`, `compression_det`, arbitrary size |
| M1.4 Schur identities and singular Gram nonnegativity | `metricGram_det_append_one`, `metricGram_det_append_two`, `metricGram_det_nonneg` |
| M1.5 Exact rank-one increment and captured-energy bound | `compression_add_rank_one_det`, `compressed_energy_le`; combined in `compressed_inverseBFGS_bound` and its finite-type version |
| M1.6 Actual principal sums and basis invariance | `PrincipalMinors.lean`; `PrincipalInvariance.principalPolynomial_coeff`, `principalSum_conjugate` |
| M1.7 Eigenbasis Gram summation bound | `diagonal_coordinate_gram_det`, `diagonal_coordinate_gram_sum_le`; `PrincipalCombinatorics.lean` |
| M1.8 Assembly without assumed determinant identities | `principalMinorHierarchy : PrincipalMinorHierarchyTarget` |

The source's combinatorial equality is not separately exported. The proof checks
the needed inequality directly by inserting a missing index into a coordinate
subset and bounding nonnegative omitted terms. This changes the proof route,
not the hierarchy's statement or constants. Larger Gram matrices and projected
compressions may be singular; only the SPD base compression is inverted.

## 2. Actual matrix-to-scalar normalization — complete

`fullBFGS_normalizedHierarchy` proves the instance with

    E(k,j) = principalSum (R.H k) j
    delta(k) = R.d k / c
    K = 4G²/c², C = G².

`metricEnergy_le_sqNorm_mul_trace` supplies the energy/trace inequality using a
PSD square root and finite Cauchy–Schwarz. Nonnegative entries, positive trace,
and terminal zero come from actual matrices. Positive dimension follows from
positive energy; it is not a new assumption.

`FullBFGSRun.beta_ge_of_weakWolfe` derives beta>=1−c2 directly from the ordinary
weak-Wolfe accepted-step inequality. `upperNull_of_tendsto` connects the vanishing
predicted-decrease limit to the scalar qualitative proof.

## 3. Qualitative reciprocal means — complete

`ScalarHierarchy` checks the shift identity including the terminal slot, positive
weighted potentials, and recurrence. `ReciprocalGrowth` retains the fixed prefix
and proves logarithmic, geometric, and arithmetic reciprocal-mean divergence.
Its reusable sequence theorem is conditional.

The exported `reciprocalGrowth : ReciprocalGrowthTarget` supplies its hierarchy
from the actual matrix theorem. No hierarchy premise remains in this export;
neither pointwise q_k→0 nor matrix convergence is assumed.

## 4. Finite horizon and superquadratic growth — complete

`QuantitativeGrowth` checks logarithmic AM–GM, telescoping, the exact real-power
finite bound, polynomial domination of the horizon-dependent potential, and
the fixed-tail horizon limit. It keeps the finite prefix explicitly and only then
sends the summable tail budget to zero.

`finiteHorizon` uses actual `R.H J`, actual tail sum `sum_i R.d(J+i)`, and the
source's constants. Its block length is m+1 with m>0, exactly the source's length
at least two. `superquadraticReciprocalGrowth : SuperquadraticReciprocalTarget`
discharges the scalar hierarchy using the actual matrix theorem.

## 5. Objective-to-matrix bridge — complete

The new run model assumes a finite convex objective, actual derivatives at the
accepted iterates, `0<c₁<c₂<1`, positive lengths, nonzero accepted gradients, the
Armijo and weak-Wolfe inequalities, and the original full inverse-BFGS recurrence.
Only the initial matrix is assumed SPD.

| Obligation | Checked implementation |
|---|---|
| Actual gradients and finite convex objective | `ObjectiveDefinitions.lean`: `gradientFunctional`, `AdmissibleBFGSRun` |
| SPD preservation from positive curvature | `inverseBFGS_posDef` |
| All run invariants from initial SPD and weak Wolfe | `fullBFGS_positive_invariants`, `AdmissibleBFGSRun.positive_invariants` |
| Same actual matrix run, with no new assumptions | `AdmissibleBFGSRun.toFullBFGSRun`, definitional q/d/beta equalities |
| Convex supporting inequality at differentiable accepted points | `convex_supporting_inequality` |
| Two-sided decrease and sublevel membership | `AdmissibleBFGSRun.predicted_decrease_bounds`, `iterate_mem_initialSublevel` |
| Armijo summability and actual tail budgets from lower-bounded values | `DescentBudget.lean`; `summable_predicted_decreases_of_lower_bound`, `tail_budget_le` |
| Finite objective-limit branch | `summable_predicted_decreases_of_value_limit`, `objectiveGrowth_of_value_limit` |
| Compactness supplies bounded gradients without gradient continuity | `convex_supporting_bound_on_compact`, `convex_gradient_bound_on_compact` |
| Objective-level qualitative, finite-horizon, and superquadratic exports | `ObjectiveEndToEnd.lean`, exact propositions in `ObjectiveTargets.lean` |

The compact-sublevel variants derive gradient and budget hypotheses. The general
variants retain explicit gradient/value bounds; the qualitative variant retains
the weaker vanishing-decrease condition. No iterate or matrix limit is assumed.

## 6. Hessian, energy, and exact determinant identities — complete

| Source statement | Checked implementation |
|---|---|
| M:hessian actual Hessian recurrence | `hessianUpdate`, `AdmissibleBFGSRun.hessian_update` |
| M:annihilation PSD and actual step kernel | `annihilatedMatrix_projection`, `annihilatedMatrix_posSemidef`, `annihilatedMatrix_mul_step` |
| Exact top determinant equality | `inverseBFGS_step_det_beta`; included in `hessianInvariants : HessianInvariantTarget` |
| M:fixedenergy exact reference identity | `AdmissibleBFGSRun.fixed_reference_energy`; actual q, t, H⁻¹, and correction definitions |
| M:energybound finite objective-gap inequality | `fixed_reference_energy_bound`; `referenceEnergy : ReferenceEnergyTarget` |
| Negligible cumulative corrections imply value convergence | `objective_tendsto_min_of_negligible_corrections` |
| Quadratic cumulative corrections imply value convergence | `objective_tendsto_min_of_quadratic_corrections`, without uniqueness |
| Unique-minimizer upgrade to iterate convergence | `quadraticCorrectionConvergence : QuadraticCorrectionTarget` |

The convergence criteria keep their actual correction-budget condition explicit.
They do not prove that this budget holds for every finite convex objective.

## 7. Localization and strict contours — complete

| Source statement | Checked implementation |
|---|---|
| Positive attained sphere gap | `Localization.sphere_gap`, with nonempty sphere justified by nontriviality |
| Radial lower bound and low-sublevel trapping | `radial_lower_bound`, `low_sublevel_subset_ball`, `trapped_in_ball_of_sphere_gap` |
| Every sublevel compact at an attained unique minimizer | `sublevel_compact`, including zero dimension |
| Any structural neighborhood contains an invariant low basin | `neighborhood_basin`, `local_basin_of_unique_minimizer`; `localization : LocalizationTarget` |
| M:strictcontours vanishing actual steps | `steps_tendsto_zero_of_strict_contour`; `strictContourSteps : StrictContourTarget` |
| Value convergence lifts to unique-minimizer point convergence | `tendsto_unique_minimizer_of_values`, `iterates_tendsto_unique_min_of_values` |

The strict-contour theorem proves the level-to-frontier implication and derives
d→0 from Armijo. It assumes no gradient subsequence or iterate convergence.
Generic localization includes Euclidean normed spaces; explicit balls on the
coordinate type `Vec n` use its default Pi norm, as recorded in the review.

## 8. Moving-frame and residual criteria — complete

| Source statement | Checked implementation |
|---|---|
| M:frameidentity actual moving-frame matrix identity | `moving_frame_energy` |
| Exact inverse-congruence trace and O(N) reciprocal bound | `normalized_frame_trace_recurrence`, `moving_frame_reciprocal_sum_bound` |
| Exact-transport arbitrary-tail contradiction | `moving_frame_tail_criterion`; `movingFrameCriterion : MovingFrameCriterionTarget` |
| Derived fixed-smooth-subspace linear Hessian trace bound | `smooth_subspace_projection_trace_update`, `smooth_subspace_projection_trace_bound` |
| Derived actual residual metric-energy bound | `smooth_subspace_residual_energy_le`, `smooth_subspace_residual_budget` |
| PSD Young and actual operator transport estimates | `FrameBounds.gram_trace_add_le`, `gram_trace_transport_le` |
| Scalar summable drift normalization and contradiction | `ResidualBudget.residual_reciprocal_sum_le`, `residual_recurrence_incompatible` |
| Actual matrix recurrence discharges the scalar hypotheses | `residual_frame_step`, `residual_frames_incompatible` |
| M:residualtheorem arbitrary-tail, source-form contradiction | `residual_frames_on_tail_incompatible_source`; `residualFrameCriterion : ResidualFrameCriterionTarget` |
| Exact Euclidean operator-norm and arbitrary-subspace representation | `FrameNorms.operatorSqBound_iff_opNorm_sq`, `orthonormal_matrix_for_subspace` |

Exact transport uses only d→0, retaining the weaker qualitative theorem. Residual
transport uses summability. The final source-form residual target adds no sign
premises, frame-rank assumption, invertible T, or whole-Hessian bound. The frame
certificate structures contain actual geometry, not an assumed scalar recurrence.

## 9. Remaining research scope

There are **no remaining obligations for the 14 registered targets or the
Module M statements mapped above**. Reusable conditional helpers are labeled as
such in the status register and their signatures.

The next work is outside the common foundation: derive the correction budgets,
exact-frame certificates, or fixed-smooth-subspace residual certificates for the
objective classes in the other research modules. Their geometric joining,
cutoff, affine-critical, and counterexample arguments remain unformalized.

There is no unconditional convergence theorem for arbitrary finite convex
nonsmooth objectives, and the source itself records negative examples. There is
no universal admissible-step existence theorem. Infinite-run results retain the
source's nonzero-gradient convention; a separate finite-termination theorem is
not exported. Conditional criteria must not be presented as unconditional
convergence of full BFGS.


## Entire-report continuation

This file retains the completed Module M source-to-proof map. The user expanded
the task to the entire report; see `ENTIRE_REPORT_PLAN.md` and
`audit/REPORT_STATUS.json` for that larger dependency and coverage register.
The first tranche adds five audited exact targets covering T's primary theorem,
H.A, scalar positive-metric convergence and actual scalar BFGS, and the radial
sufficient condition. Detailed inventories identify secondary claims still open.
The entire-report completion flag remains false.

The second tranche adds seven exact targets (26 total) and the secondary
consequences mapped in `audit/REPORT_GEOMETRY_STATEMENT_REVIEW.md`. H.B is checked;
H.C remains open. RS/SP equivalence and IR sufficiency are checked; full RS-to-IR
remains open. Incoming-jump obstruction and scalar characterization are checked;
G examples, feasibility and geometric interpretations remain open. Inventories
now include F, A, C/U and proof designs for D/L. Entire-report completion remains
false; the 26-target success is not a claim that every chapter is verified.

Third tranche: 36 exact targets pass (760 explicit / 1,069 total declarations).
RS/IR and local central equivalence, nonunique basin, exact affine lifting,
homogeneous and linear-correction rates, both scalar examples and finite pair
claims are checked. The logarithmic rate criterion retains an actual correction
bound; the quadratic-gauge family is not yet discharged. F/R structural
applications, T affine covariance/Q separation, G remaining geometry, H.C,
C/U/A, D/L and the synthesis closure remain explicit obligations.

## Fourth milestone: structural applications and geometric scope

The pinned full build and transitive audit pass for 996 explicit / 1,384 total
theorem declarations and all 44 exact targets. The fourth tranche adds the
actual centered and quadratic-gauge families, affine covariance, main planar
H.C, G ellipsoid/pointwise/accessibility geometry, and Q foundations through
Q.13. Statement and peer reviews are collected in
`audit/REPORT_APPLICATIONS_STATEMENT_REVIEW.md`; actual logs are
`audit/report_applications_check.log`, `audit/build.log` and `audit/axioms.log`.

The G.4 correction distinguishes accessible and all-active jump spans. Its
precise accessible-span consequence is proved, the full-active version keeps
its necessary qualification explicit, and the algebraic countermodel is not
misrepresented as an objective example. Original research sources remain
unchanged. `audit/REPORT_STATUS.json` records this separately.

Next independent work is Q's derived finite-envelope calibration and uniform
compensated transport, H's remaining block/low-rank/relative-interior clauses,
and F's transformed-gauge family. Remaining R/F applications, C/U/A and D/L
constructions, and synthesis/evidence closure are still obligations. Entire-report
verification remains false; no generic conditional criterion is counted as its
undischarged objective-specific application.

## Fifth milestone: parabolic and transformed families, H.8, and G.4 correction

The pinned full build and compiled-environment axiom audit pass for 1,202
explicit / 1,675 total theorem declarations and all 52 exact targets. Logs are
`audit/report_families_check.log`, `audit/build.log` and `audit/axioms.log`.
Only propext, Classical.choice and Quot.sound occur; every audited source hash
matches. See `audit/REPORT_FAMILIES_STATEMENT_REVIEW.md` and its linked reviews.

Q's arbitrary original finite family now has a derived actual θ²rrᵀ certificate
and full-BFGS value/iterate convergence. Uniform calibration, denominator,
logarithm and transport data are proved before all eligible pairs. The explicit
three-branch objective has actual SPD first-step witnesses, arbitrarily small
eligible decreases and unbounded radial quotients on a fixed positive band in
every neighborhood. The printed c1≤2/3 pair scope and the all-c1 rho extension
are distinguished. Literal ordered pruning and printed-field identification
remain separately tracked source-description obligations.

F:transform is proved including literal inverse/Theta' formulas and endpoint
gauge differentiability. H.8 has both the full-slope and actual recurrent-tail
convergence conclusions, derived coordinates and exact initial/current metric
fiber limits. H.7.4 and remaining H class bookkeeping are next-tranche work.

G.4's missing accessibility qualification now has an actual convex-objective
counterexample: shiftedAbs with (c1,c2)=(1/8,1/4), a continuous constant-I band
certificate and genuine limiting gradients whose full-active tangent is zero.
Accessible jumps are zero for these constants. The qualified accessible-span
statement remains valid. Original sources are unchanged; the correction and
example scope are recorded in `audit/G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md`.

Entire-report verification remains false. Remaining F/R applications, G
interpretations, C/U/A, D/L constructions and final synthesis/evidence coverage
remain explicit obligations. Next-tranche drafts live only under audit/scratch
and are excluded from this release manifest until fully integrated and audited.

## Sixth milestone: finite structural families and source closure

The pinned full build and compiled-environment audit passed for **1,445 explicit
and 2,014 total theorem declarations**, with all **61 exact targets** inhabited
and only propext, Classical.choice and Quot.sound in transitive dependencies.
The exact 177 source hashes match the audited bytes. Actual logs are
`audit/report_structures_check.log`, `audit/build.log`, `audit/axioms.log`;
statement scope is reviewed in `audit/REPORT_STRUCTURES_STATEMENT_REVIEW.md`.

Q's original-family theorem and every internally retained source construction
are now mapped, including literal ordered pruning, printed scale and strict
acceptance identities. H's internal H.7.4/class/energy statements are now proved;
its cited earlier three-gradient construction and external two-piece termination
result remain cross-references to reconcile. The rank-at-least-three open
question remains classified as a conjectural gap, not as a theorem.

F's actual max-affine active reduction, literal extended-real threshold and
tail basin are proved, as is the actual coercive five-piece finite line-search
obstruction in every neighborhood of its unique minimizer. R's arbitrary mixed
gauge powers, actual finite polyhedral C1,1 extensions and smooth-plus-PLQ basins
are proved. Extensions need not be convex off their cells. The proof derives
one-sided radial matching; the source's stronger full-gradient boundary assertion
is separately pending. No matrix/iterate convergence or algorithm modification
was added to any family theorem.

The A barycentric Gram-inverse and local affine-independence/positive-coefficient
geometry is checked, but its application to actual finite smooth-max subdifferentials
is still a separate obligation in this frozen release. New scratch proofs do not
change the verified status until integrated and audited.

Entire-report verification remains false. Continue with the explicit matrix-limit
run, finite-ray-singularity step existence, residual decompositions, R branch and
spectral boundary cases, A/C/U, D/L and source synthesis. Review and push the
milestone, then continue these independent proof chains autonomously.
