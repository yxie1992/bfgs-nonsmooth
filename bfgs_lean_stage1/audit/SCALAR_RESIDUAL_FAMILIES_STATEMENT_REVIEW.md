# Scalar affine residual families: statement and dependency review

## Source and result

Original sources are unchanged: `report/chapters/R.tex`, subsection “Polyhedral losses and penalties at nonzero solutions”, and `report/chapters/families.tex`, the finite-full-space-ray-singularity paragraph (line 159 in the reviewed version).

The final main import is `BfgsVerification.ScalarResidualFamilies`, importing `AffineKinkCells` and `AffineKinkAlgebra`. Its namespace is `BfgsVerification.AffineKinks`.

The primitive `Kink` is the actual convex two-slope affine-residual function `max (lo * (a·x-b)) (hi * (a·x-b))`, with only `lo ≤ hi`. Actual absolute value, hinge and quantile identities are proved from those data. Every finite family has a checked cover by actual closed convex sign polyhedra; on each cell the penalty equals an explicitly affine smooth piece. This derives the source representation rather than assuming it.

`local_kink_basin` derives a positive objective gap basin from the actual local representation, local C1,1 smooth loss, finite globally convex full objective, and an attained unique global minimizer. Every actual admissible full-BFGS run starting below that gap stays in the prescribed neighborhood and has both objective values and iterates converging to the minimum. There is no assumed convergence, sign identification, matrix convergence or component-gradient continuity. Separate convexity of the smooth loss is unnecessary; the full objective convexity hypothesis suffices.

The literal exported basin wrappers are `local_absolute_basin`, `local_hinge_basin`, `local_quantile_basin`, and `local_matrix_l1_basin`. The last uses an arbitrary actual rectangular matrix and residual `A.mulVec x - b`, thus includes generalized and fused linear residual data. A separately named first-difference matrix example has not been added. Quantile slopes are ordered for any real quantile parameter; this strengthens the usual [0,1] parameter domain without changing the minimum/convex full-objective hypotheses.

## Line-search existence

`sum_component_supports_equal` proves that differentiability of a finite convex sum forces all supporting vectors of each component to agree. This yields `initial_residual_ne_zero` for each genuine kink directly from differentiability of the penalty. The proof does not assume that individual residuals are nonzero. Trivial components (zero affine coefficient or equal slopes) are handled separately.

`penalty_finite_bad_ray` and `objective_finite_bad_ray` prove finiteness of the actual full-space nondifferentiability times on every ray, including zero and parallel directions. The smooth objective term need only be globally differentiable. The initial differentiability of the whole objective implies initial penalty differentiability by subtraction, so there is no added nondegeneracy premise.

`fullBFGS_step_of_representation`, `absolute_fullBFGS_step_exists`, and `hinge_fullBFGS_step_exists` conclude a positive step with an actual full-space Fréchet derivative and strict Armijo and strict weak-Wolfe inequalities, for every actual SPD initial metric and nonzero actual gradient, 0<c1<c2<1, and an actual lower bound along the nonnegative search ray. These wrappers apply the independently proved finite-bad-ray line-search theorem after deriving its class hypothesis. They do not claim an implementation complexity guarantee or existence at a zero gradient.

## Scope boundaries

The convergence statements are local low-sublevel basins under uniqueness, exactly the source application. They are not arbitrary-start global convergence statements for these uncentered families. The explicit local centered/noncentered scalar decomposition is not separately exported; the basin is proved using the stronger actual finite sign-cell representation. Arbitrary extended-valued constraints and non-Euclidean spectral residual smoothness are not included. Euclidean residual finite-bad-ray existence remains a distinct subsequent class bridge.

## Compiler and axiom evidence

All three main modules passed the pinned toolchain build. `ScalarResidualFamiliesAudit.lean` prints transitive axioms for all 51 explicit declarations: 38 theorems, 12 definitions and the `Kink` structure. The actual compiler output contains only `propext`, `Classical.choice`, and `Quot.sound`; no mathematical axioms or proof bypasses occur. See `scalar_residual_families_axioms.log`, `scalar_residual_families_validation.log`, and each named build log. SHA256 source and audit hashes are recorded in the validation log. These additions postdate the seventh whole-project milestone f820c46 and await the next global audit.
