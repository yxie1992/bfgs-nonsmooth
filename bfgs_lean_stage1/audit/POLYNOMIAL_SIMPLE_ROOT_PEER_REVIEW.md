# Independent polynomial simple-root review

Reviewer: convex_gradient. Read all six frozen Lean sources and inspected the actual declaration/axiom log, three strict target checks, validation report, and source hashes. All six hashes match the delivered manifest. No statement or mathematical defect found in this bounded scope.

The augmented map is the actual map `(x,t) ↦ (x,F(x,t))`. Its derivative is proved injective from the actual nonzero vertical derivative; finite-dimensionality supplies the continuous linear equivalence. The local inverse theorem then produces the selector and both inverse identities. No selector or invertibility hypothesis is inserted as an extra premise.

The fiber is the actual univariate polynomial obtained by evaluating parameter coordinates and retaining the scalar variable. Its evaluated derivative is proved equal to the actual vertical Frechet derivative by composing with `(x,t)` and using derivative uniqueness. The argument places no degree limit on the polynomial and permits arbitrary finite parameter dimension, including dimension zero.

The box theorem chooses positive parameter and scalar radii before quantifying over all parameters and scalar candidates. The selector remains inside that same fixed scalar interval; both directions of the root equivalence are proved. Smoothness holds throughout the parameter ball. The norm is the project's standard finite Pi norm, whose open balls are finite coordinate-band intersections; this is exactly the semialgebraic set proved, with no Euclidean-ball convention mismatch hidden in the statement.

The graph identity is an actual equality with the polynomial zero set intersected with the parameter ball and scalar band. The projection identity uses the constructed root for every point of the parameter ball and yields the entire ball. Neither step uses a global projection-closure axiom or an assumed semialgebraic selector. The final Prop contracts retain the original root and nonzero fiber-derivative hypotheses, the fixed radii, all root candidates, and the graph/projection conclusions.

The delivered audit contains 26 actual declaration reports with only `propext`, `Classical.choice`, and `Quot.sound`; all three exact contract checks pass. This proves local regular-root chart and local projection infrastructure only. Singular roots, arbitrary global projections, stratification, curve selection, and the full Module A semialgebraic path argument remain separate obligations. The supplied statement review correctly preserves that boundary.


Main delivery preserves every proof and statement; only owned imports are qualified. See `a_polynomial_simple_root_copy_validation.log`, the main manifest and the fresh pinned main build/type/axiom/contract/validation logs.
