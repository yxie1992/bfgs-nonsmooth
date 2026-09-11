# Q three-branch example: statement and dependency review

The three `ParabolicExample*.lean` files formalize the actual finite maximum
`max(max(u²+v,3u²),2u²-v)` via an explicit `Parabolic.Family 3`.
The exact equality with this maximum is checked, so family convexity,
compact sublevels, and unique minimum apply to this concrete objective.

## Proved example and separation

`ParabolicExamplePairs` derives the actual objective derivatives at both
strict-cell endpoints from local equality with actual branches. It proves
the exact values, decrease, curvature, radial numerator, SPD matrix, and
unit ordinary BFGS step for the generalized pair. Neither eligibility nor
a matrix recurrence is assumed in the final example conclusions.

`printed_armijo_iff` states the exact printed-pair range `c1<=2/3`.
The generalized parameter is chosen for every `c1<1`; its mathematical
scope and relation to the printed example are documented separately in
`PARABOLIC_EXAMPLE_SOURCE_SCOPE.md`. No original source was changed.

`radial_quotient_tendsto` is literal filter divergence to `atTop` as
positive epsilon tends to zero, for every fixed nonzero horizontal
coordinate and positive rho. The actual predicted decrease tends to zero.
The positive-level and neighborhood assertions do not require a gradient
at the limiting tie point.

`eligible_radial_unbounded_on_neighborhood` first chooses one positive
band, then for every positive decrease threshold and every candidate
radial constant constructs actual differentiable eligible endpoints in
the given neighborhood, an SPD metric and its exact unit step, and a
strict violation of the radial bound. Its assumptions `c1<1,c2>=0`
include every original allowed pair `0<c1<c2<1`. The band is not allowed
to shrink with the candidate constant or threshold.

`not_radial_secant_on_neighborhood` refutes the original
`HasRadialSecantBounds` on every neighborhood of the origin.
`not_radial_secant_on_sublevel` gives the same statement on every positive
sublevel. These use actual endpoints, positive curvature and the original
ordered-value quantifiers. They do not depend on a custom replacement
definition of RS.

`converges_without_radial_secant` combines this failure with the principal
Module Q theorem for every actual admissible full-BFGS run on this exact
objective. Each counterexample pair has its own explicit SPD initial
metric; no single infinite run containing all the counterexample pairs
is asserted.

## Contrasting correction and scope

The printed piecewise `sourceScale` is defined explicitly. Its exact old
and new endpoint values are proved, as are the global positive-level
bounds `exp(-1/3)<=sourceScale<=1`. The actual direction numerator is
`2*rho*epsilon`; its quotient is `4*rho²*epsilon/(1+rho)` and tends to
zero. At the new endpoints the source scale is one, so this is precisely
the source's transported secant calculation. At rho=1/2 it specializes to
`2*epsilon/3`. The unscaled quotient multiplier is exactly one, and
`source_compensated_log` proves the printed exact logarithmic formula
`epsilon/(6*(3*u²+epsilon))`, independently of rho.

Continuity of this separately normalized *printed piecewise* field across
both interfaces is not yet exported in these example modules. The
selector-free calibration field's continuity across all interfaces and
the actual band certificate are already proved by the general Q modules;
the example run-convergence theorem uses that derived field. Identifying
the printed piecewise field with the general calibration up to constant
rescaling, or independently proving its continuity, remains a small
explicit-source presentation obligation, not a premise of the convergence
or separation results.

## Verification evidence

Pinned main Lake build: `parabolic_example_contrast_build.log`, which
imports and builds all three modules. The scoped declaration list and
axiom log are `parabolic_example_declarations.txt` and
`parabolic_example_axioms.log`. Three exact expected-type examples are
checked in `PARABOLIC_EXAMPLE_CONTRACTS.lean`, with compiler output in
`parabolic_example_contracts.log`. Source checks and exact axiom coverage
are recorded in `parabolic_example_validation.log`.
