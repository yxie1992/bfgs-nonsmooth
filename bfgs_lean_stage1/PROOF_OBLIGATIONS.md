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

## 5. Remaining scope, distinct from completed targets

There are **no remaining obligations for the three original targets or the
requested finite-horizon matrix-run bound**. Reusable conditional helpers are
labeled as such in the status register and their signatures.

Outside these targets, an objective-level formal model and deductions from finite
convexity, differentiability of accepted iterates, Armijo, compactness, and finite
limiting objective value have not been implemented. Other Module M energy,
localization, and residual statements and the other research modules also remain
outside this verification. The source's separate exact top-determinant update
identity is not an exported result here; the requested hierarchy includes its
top-degree inequality.
