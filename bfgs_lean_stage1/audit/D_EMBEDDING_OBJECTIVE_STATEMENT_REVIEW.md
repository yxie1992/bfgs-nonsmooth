# Module D concrete two-dimensional objective: statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/D.tex`, main theorem and section “The single objective with bad starts arbitrarily near its minimizer” (equation D:fullobjective, branch regularity, compact sublevels, and nonsmooth minimum). Original research sources are unchanged.

Scope: `BfgsVerification/DEmbeddingObjective.lean`, namespace `BfgsVerification.DEmbedding`; 54 declarations (48 theorems and 6 definitions). This unit is a concrete objective/branch prerequisite. It does not itself assert existence of the failing BFGS runs or the deterministic trial embedding. Those are separate root-owned obligations. This unit was developed in scratch during the ninth audit and integrated only after its committed milestone cad9aab and freeze release. Scratch source and audit backups are retained.

## Actual definitions and quantifiers

`bStar = 2*seedC-32*seedD` uses the exact algebraic seed constants. The root certificate gives `33 < bStar < 34`; no floating-point choice replaces the root. `parameter` is the actual vector `[2,2,bStar]`. `branch` is the four actual functions from D:fullobjective and `objective` is their actual finite supremum. `objective_literal` proves the coordinate formula with the three actual scalar functions and the fourth coordinate branch. There is no oracle, smoothness, Hessian, or convergence assumption on the objective.

`branch_convex` and `branch_contDiff` apply globally to every index in `Fin 4`. `objective_unique_minimum` states actual value zero at the origin, global nonnegativity, and equality only at the origin. Every real sublevel, including an empty one, is compact. This is derived by finite-dimensional convex localization from the attained unique minimum, so no boundedness premise is imported into the conclusion.

## Actual derivatives and matrix norm

`ridge_hasFDerivAt` and `ridge_second_hasFDerivAt` identify both actual Frechet derivatives, using the already verified scalar derivatives. `ridge_hessian` and `branch_old_hessian` identify the matrix of the actual derivative of the actual first derivative with the scalar second derivative times the actual outer product. `branch_last_hessian` proves the fourth Hessian is zero. `RadialHessian.matrix` is not an independently supplied matrix field.

`branch_hessian_bounds` proves matrix positive semidefiniteness of the Hessian and of `(64 : real) I - Hessian`, at every point and for all four branches. `branch_hessian_opNorm_bound` gives the corresponding actual Euclidean operator-norm upper bound. `branch_individual_hessian_bounds` also proves the literal source estimates: first branch at most 51, second at most 51*(65/64) and strictly below 52, third strictly below 12, and fourth zero. The third estimate uses the actual seed inequality c^2+d^2 < 2.

`branch_hessian_lipschitz` has unrestricted point quantifiers and bounds the Euclidean operator norm of the actual Hessian difference by 60000 times the Euclidean distance of the points. The coordinate space otherwise carries Lean’s finite-Pi topology; the displayed matrix norm is `FrameNorms.euclideanOpNorm` and the displayed vector norm is explicitly `norm (euclideanVector (x-y))`. Thus the numerical constants are asserted in the source Euclidean convention. The proof derives the bound from the scalar global Lipschitz constant, an explicit rank-one operator estimate, and finite-coordinate Cauchy–Schwarz. Its intermediate bound 8*(139264/20)=55705.6 is below 60000; it does not assume a uniform gradient modulus or an external numerical computation.

## Nonsmoothness and source directional derivative

`objective_not_differentiable_zero` proves failure of actual Frechet differentiability. It uses the two distinct actual supporting vectors zero and the second coordinate vector, each obtained from global inequalities for this objective. Independently, `objective_directional_derivative_zero` proves the literal one-sided quotient limit F(th)/t -> max(0,h[1]) as t decreases to zero through positive values, for every actual direction. Here index 1 is the source’s second coordinate. The derivative is derived from the three actual zero first derivatives and the finite maximum identity, without assuming a branch switching pattern.

## Export and remaining construction

`objective_function_contract` packages the actual finite-max definition, all convex C2 branches, convexity and unique zero of the objective, all compact sublevels, nonsmoothness and directional derivative at zero, and the global 64I/60000 Hessian bounds. `objective_literal` and `branch_individual_hessian_bounds` retain the more detailed source formulas separately.

The local cone at p_n, its strict plateau derivative identities, exact embedded trial values/gradients, deterministic accepted orbit, nonstationary failure point, and all-trial small-neighborhood conclusions are not claimed by this prerequisite. No correction of the source mathematical conclusions was required for this unit. The preceding scalar construction was proved on the larger parameter interval [2,34], which contains both literal source parameters.

## Verification

The importing main build log is `d_embedding_objective_build.log`. The scoped audit `DEmbeddingObjectiveAudit.lean` imports the main source and prints transitive axioms for all 54 declarations; `d_embedding_objective_axioms.log` records the output. `d_embedding_objective_validation.log` records matching declaration names, allowed-axiom checks, the forbidden-token scan, and artifact hashes. This unit is not part of the frozen ninth whole-project result; subsequent integration requires the next whole-project audit.
