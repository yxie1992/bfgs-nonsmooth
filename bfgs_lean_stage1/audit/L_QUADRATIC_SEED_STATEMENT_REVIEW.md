# Module L concrete quadratic seed: statement review

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/L.tex`, the global theorem's objective and inherited-seed/minimizer paragraph, especially equation L:eq:minimizer. Original sources are unchanged.

Module: `BfgsVerification/LQuadraticSeed.lean`, namespace `BfgsVerification.LQuadraticSeed`. There are 56 declarations: 48 theorems and 8 definitions. The only assumption of the final `quadratic_seed_contract` is `0 < mu`; the slopes are the already verified exact algebraic seed constants, not additional free parameters.

## Literal geometry

The actual objective is mu/2 times the actual Euclidean sum of squares plus the actual three-slope seed maximum. `objective_eq_sup` identifies it with the actual maximum of the three concrete branches. The weight identity for gbar is exactly 129/257 and 128/257 on g0 and g1. `gbar_dot_first`, `gbar_dot_third`, and `gbar_sqNorm` prove the two equal pairings and strict third pairing with the literal 1/257 constant.

`gbar_mem_convexHull`, `gbar_least_sqNorm`, `gbar_least_norm`, and `gbar_unique_least_sqNorm` concern the actual convex hull of the three actual slope vectors. The Euclidean norm is explicit, so the finite-Pi ambient norm is not substituted for the source norm. Convex-hull membership is proved from the displayed positive weights; minimality follows from the supporting halfspace and Cauchy-Schwarz; equality is unique.

The minimizer is the actual vector `(-mu^(-1)) • gbar`; `minimizer_coordinates` also gives (-1/(257mu),16/(257mu)). Its actual objective value is -1/(514mu). A completion-of-the-square lower bound proves it is the unique global minimizer; coercivity is the standard `Tendsto objective (cocompact ...) atTop`, and every real sublevel is compact. The minimizer is nonzero.

`minimizer_active_iff` states, in both directions, that precisely indices 0 and 1 are active. The third strict gap is separately exported. Actual nondifferentiability at the minimizer follows from the distinct gradients of these two active lower contacts and uniqueness of a supporting vector at a differentiable point. No generic maximum differentiability assertion is assumed.

## Curvature, norms, and actual subdifferentials

The module proves global Euclidean mu-strong convexity both with the project's explicit sum-of-squares definition and with mathlib's `StrongConvexOn` on `EuclideanSpace`. Each branch is globally convex and C2. `branch_hasGradient` is an actual Frechet derivative theorem; `branch_second_hasFDerivAt` differentiates the actual first derivative. `branch_hessian` concludes the actual second-derivative matrix equals mu I globally, rather than introducing a prescribed Hessian field.

`origin_subdifferential` identifies the actual global convex subdifferential with the full seed slope triangle. It applies the verified finite-max subdifferential theorem to the actual branch derivatives and proved finite-max representation. `origin_nonstationary` proves zero is outside that subdifferential. The objective value at the origin is exactly zero.

## Scope boundary

`quadratic_seed_contract` packages the objective, branch regularity/Hessians, Euclidean strong convexity, coercivity/compact sublevels, exact least-norm point and weights, exact unique nonsmooth optimizer, and origin nonstationarity. It makes no BFGS orbit assertion. In particular, the exact unperturbed seed orbit is not asserted to remain an orbit after adding the quadratic. The five-dimensional normalized return map, actual deterministic neighborhood agreement, certified derivative spectrum, and nonlinear stable-orbit existence remain separate obligations. This distinction is required by the source itself.

## Compiler and axiom evidence

Scratch source compiled without errors before integration after the ninth freeze was released. Main importing build: `audit/l_quadratic_seed_build.log`. Scoped audit: `audit/LQuadraticSeedAudit.lean`, `audit/l_quadratic_seed_axioms.log`; declaration list: `audit/l_quadratic_seed_declarations.json`; validation and hashes: `audit/l_quadratic_seed_validation.log`. The next whole-project audit must integrate this unit; it is not part of the frozen ninth result.
