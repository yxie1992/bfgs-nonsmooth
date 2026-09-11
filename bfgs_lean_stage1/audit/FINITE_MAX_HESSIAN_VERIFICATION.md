# Generic finite-maximum Hessian calculus for Module L

This five-file tranche proves the calculus needed to pass the source's branch
smoothness bound to the actual maximum wherever that maximum has two derivatives.
It does not instantiate the literal L objective or claim an additional BFGS
counterexample. The five compiler-clean files are delivered in `BfgsVerification/`; the original audited scratch snapshot remains as a backup.

## Exact hypotheses and conclusions

* `LocalFiniteMax F f x` is the existing actual local maximum representation:
  every sufficiently nearby objective value is the greatest element of the
  range of the finitely many branch values, including attainment. There is no
  supplied active set or assumed gradient alphabet.
* `hg` supplies actual first Frechet derivatives of every branch at every point,
  represented by Euclidean coordinate gradients. `hlip` is exactly
  `sqNorm (g i z - g i w) <= L^2 * sqNorm (z-w)`, with `0 <= L`.
  Thus the norm is the source's Euclidean norm, not the ambient Pi/sup norm;
  there is no dimension-dependent loss in L.
* `active_derivative_eq` derives equality of every active branch derivative to
  the derivative of the actual maximum by Fermat's theorem on their nonnegative
  local difference. No branch or objective convexity is used for this fact.
* `gradient_increment_bound` invokes the already verified inactive-gap theorem,
  obtains an actual maximizing index at each nearby point, and uses its activity
  at the base plus actual derivative equality. The increment estimate is proved
  only where the full maximum is differentiable, without assuming global
  smoothness or global Lipschitz continuity of its gradient.
* `branch_upper_taylor` proves the exact L/2 Euclidean upper Taylor model by a
  one-dimensional derivative/mean-value argument along the actual straight ray.
  `finiteMax_local_upper_taylor` derives the same local model for the actual
  maximum by the inactive-gap argument. Both allow nonconvex branches and full
  objectives; no Taylor model is an input.
* `second_upper_of_increment` and its lower counterpart use the actual derivative
  of a derivative field at the base, followed by a positive scalar slope limit.
  They do not require continuous second derivatives or external Taylor expansion.
* `finiteMax_actual_hessian_bounds` returns symmetry and
  `mu*sqNorm v <= dot v (H.mulVec v) <= L*sqNorm v` for every vector, where H is
  literally `RadialHessian.matrix F x`, built from the actual second Frechet
  derivative's coordinate entries. The lower estimate is derived from the full
  objective's strong convexity and actual supporting inequalities.

The final Hessian contract spells out the conventional local meaning of two
Frechet derivatives: the first derivative exists near x and its derivative
exists at x. It does not infer meaningful derivatives merely from Lean's total
`fderiv` values at nondifferentiable points. No C2 continuity is assumed.
The auxiliary `actual_second_eq` also identifies any actual derivative field
with the literal second derivative under the same local hypothesis.

No dimension is assumed positive. Empty branch families cannot satisfy the
actual attained local-maximum representation, so no separate nonemptiness
premise is inserted. The lower result allows arbitrary real mu; applications
with positive strong-convexity constant specialize directly.

## Source scope and remaining application

Module L's concrete branch formulas must still provide their actual gradients,
Euclidean Lipschitz constant and strong convexity to instantiate this generic
result. Those are owned by the parent agent. This tranche makes no claim that
the nonsmooth maximum has a globally Lipschitz gradient, no claim that it is
twice differentiable at every point, and no iterate/matrix/line-search premise.
The two strict contracts are generic calculus contracts, not two additional
literal-objective convergence/failure statements.

The reproduction script rebuilds all five files in dependency order, audits
all explicit declarations' actual types and transitive axioms, checks the two
contracts with `Meta.isDefEq`, and verifies source hashes. Standard foundation
axioms only are permitted by the validator. Mathematical sources are unchanged.


## Main-library delivery

The compiler-clean frozen snapshot was copied to `BfgsVerification/` after milestone 11. Only local import names changed to delivered main-library module names. Fresh main hashes, exact declaration/axiom drivers, and contract logs use the `finite_max_hessian` prefix in `audit/`. Reproduce with `bash audit/verify_affine_spatial_hessian.sh`; it uses no scratch source or object file. Original snapshot and peer-review evidence remain available. The scoped main manifest, not the old scratch hashes, describes the delivered source bytes.
