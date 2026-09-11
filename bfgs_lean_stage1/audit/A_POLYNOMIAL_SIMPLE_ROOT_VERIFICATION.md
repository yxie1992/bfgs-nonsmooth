# Parameter-uniform polynomial simple-root charts

This six-file, 26-declaration scope proves a genuine nonlinear local chart/projection case toward Module A's outstanding general semialgebraic infrastructure. The reviewed source is delivered in the main library; the original scratch snapshot is preserved. The final research theorem is not replaced by a local or regularity-conditioned statement.

## Inputs and exact conclusions

The final theorem accepts an arbitrary `MvPolynomial (Option (Fin n)) ℝ`, with arbitrary finite parameter dimension n and arbitrary degree. The `some i` coordinates are parameters and `none` is the scalar coordinate being eliminated. It assumes only that b is an actual root of the actual fiber polynomial at a and that the derivative of that fiber polynomial at b is nonzero.

It constructs one function g and positive radii r, δ such that:

- g(a)=b and g is `ContDiffOn ℝ ∞` on the entire parameter ball B(a,r).
- For every x in that ball, g(x) lies in the fixed scalar interval of radius δ about b.
- For every x in that ball and every scalar t in that fixed interval, P(x,t)=0 if and only if t=g(x).
- The actual graph of g restricted to the parameter ball is semialgebraic in the existing Boolean-polynomial sense.

The radii precede all parameter and candidate-root quantifiers. A separate theorem proves that the existential projection of the actual polynomial zero set restricted to these boxes equals the entire parameter ball, and hence is semialgebraic. There is no assumed selector, local uniqueness, semialgebraic graph, or nonlinear projection closure in these final contracts.

## Actual proof chain

`PolynomialFibers` defines the actual multivariate evaluation and actual univariate fiber through ring-hom substitution. It proves equality of their evaluations. Analyticity comes from evaluation of the actual multivariate polynomial along continuous linear coordinate maps. The actual vertical Frechet derivative is identified with the actual fiber-polynomial derivative using chain rules, the ordinary polynomial derivative theorem and derivative uniqueness. Thus nondegeneracy is a checked polynomial derivative condition, not a supplied derivative oracle.

`SimpleRootInverse` augments F(x,t) to (x,F(x,t)). Its derivative is injective when the actual vertical derivative is nonzero: after the parameter coordinates vanish, linearity reduces the remaining coordinate to t times that nonzero derivative. Finite-dimensionality constructs the continuous linear equivalence, and the actual inverse function theorem produces the implicit root germ and local uniqueness. No preexisting root function is assumed.

`SimpleRootBox` uses the smooth germ and its actual uniqueness neighborhood to choose fixed positive radii before all nearby x and t. The use of `ContDiffAt` at analytic order supplies one neighborhood on which all finite derivative orders hold. The product distance is the maximum of the parameter and scalar distances; the uniform root characterization therefore holds throughout the stated product box.

`SemialgebraicRootBoxes` proves coordinate bands and finite parameter balls are actual finite Boolean polynomial sets. Its graph identity is exact: within the parameter ball, the graph equals the intersection of the polynomial zero set with the fixed scalar band. Both directions use the derived root characterization, including containment of g(x) in the band. `PolynomialSimpleRoot` discharges all generic smoothness, derivative, selector and uniqueness conditions from the original polynomial/root inputs.

## Exact targets and scope boundary

The contracts are `PolynomialFiberDerivativeTarget`, `PolynomialSimpleRootChartTarget`, and `PolynomialSimpleRootProjectionTarget`; all are supporting real-algebraic results. The graph is asserted semialgebraic only on the constructed parameter ball. The function is proved smooth there; an explicit `AnalyticOnNhd` conclusion for the selector is not asserted. The ball uses the existing Pi norm on the finite coordinate space, hence is a box with finite polynomial inequalities.

This does not prove global nonlinear projection closure. Multiple roots, roots escaping to infinity, degree changes, singular strata, and a finite parameter partition remain unresolved. Nor does this prove the general semialgebraic path decomposition or Module A's finite affine-critical-value theorem. The new result supplies the regular simple-root local-chart ingredient without assuming those missing global results.

## Reproduction

Run `bash audit/verify_a_polynomial_simple_root.sh`. The script builds all six files with the pinned Lean toolchain, prints all actual types and transitive axioms, checks the three target types by strict `Meta.isDefEq`, and validates all six frozen SHA-256 source hashes. The allowed transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. No external mathematical computation or root-location oracle is used. Evidence is recorded in `source_hashes.json`, `declarations.txt`, `SIMPLE_ROOT_AXIOMS.lean`, `SIMPLE_ROOT_CONTRACTS.lean`, and the build/axiom/contract/validation logs.


## Main delivery

The six delivered main sources differ from the reviewed scratch snapshot only by qualifying owned imports with `BfgsVerification.`. The self-contained main driver, manifest and logs are `verify_a_polynomial_simple_root.sh`, `a_polynomial_simple_root_declarations.json` and `a_polynomial_simple_root_{build,axioms,contracts,validation}.log`. The driver needs no scratch sources or scratch proof imports. Main source hashes are independently frozen in the delivered manifest.
