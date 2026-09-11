# Module A: barycentric algebra and local stability

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/affine_geometry.tex`, the local nondegenerate smooth-max discussion. Original source unchanged.

The compiler-checked import is `BfgsVerification.AffineBarycentricLocal`, through `AffineBarycentricAlgebra` and `AffineBarycentricCoordinates`. These three files contain 19 theorems and five concrete definitions. The actual build is recorded in `affine_barycentric_full_build.log`; `A_BarycentricAxiomChecks.lean` and `affine_barycentric_axioms.log` check all 24 declarations. Every transitive axiom list is contained in `propext`, `Classical.choice`, `Quot.sound`.

The matrix theorem constructs the Gram matrix, its inverse, and the unique coefficient formula. Positive definiteness, determinant nonvanishing, persistence of full column rank, continuity of the formula, and positivity of every nearby solution are proved. Nearby solvability is not assumed or inferred: a nearby augmented system may be inconsistent.

The augmented matrix uses columns `(1,g_i)`; moving the scalar coordinate from last to first is just a coordinate convention. Its injectivity is proved equivalent to actual affine independence. Its equation against `(1,0)` is proved equivalent to coefficients summing to one and a zero weighted gradient sum.

`affine_critical_subfamily_eventually_full` assumes only continuity of each gradient map at the base point, affine independence at that point, and strictly positive zero barycentric weights. It concludes that nearby gradients remain affinely independent and that **every** finite index subset whose actual affine hull contains zero is the whole index set and has zero in its actual convex hull. Coefficients on a subfamily and their zero extension to all indices are derived from affine-span membership. No gradient or index is silently discarded, no rank persistence is a premise, and no coefficient sign is assumed away from the base point.

This is the geometric part of the source's local no-false-affine-criticality result. Its application to actual subdifferentials still requires the independently assigned local finite smooth-max subdifferential formula and elimination of branches inactive at the base point. Canonical affine geometry, the rank-loss example, lower semicontinuity of affine distance, and semialgebraic finite-critical-values arguments are separate obligations; this tranche does not claim all of Module A.
