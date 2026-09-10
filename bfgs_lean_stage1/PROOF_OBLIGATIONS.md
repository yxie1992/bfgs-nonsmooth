# Module M source-to-proof register

**All original M.1–M.3 matrix-run targets are proved, compiled, and axiom-audited.**
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

## 6. Remaining scope, distinct from completed targets

There are **no remaining obligations for the three original targets or the
requested finite-horizon matrix-run bound or the objective bridge above**. Reusable conditional helpers are
labeled as such in the status register and their signatures.

Other Module M energy, localization, and residual statements and the other
research modules remain outside this verification. There is no theorem of
admissible-step existence on every search ray or of overall optimal-value
convergence. Infinite-run results assume nonzero gradients at all accepted
iterates; a separate finite-termination theorem is not exported. The source's
separate exact top-determinant update
identity is not an exported result here; the requested hierarchy includes its
top-degree inequality.
