# Source R almost-everywhere Hessian warning: actual counterexample

Integrated into the main library after eighth milestone 01c1511. Original research remains unchanged. The eighth frozen whole-project audit does not include these additions; the new main build and independent importing audit are recorded here.

`RadialSingularCurvature.lean` uses the actual existing shifted scalar objective F(x)=(x+2)²/2+|x| and its actual one-coordinate embedding, with attained unique minimizer −1 and minimum 3/2. The existing proof establishes modulus-one strong convexity and compact sublevels.

The actual second scalar derivative equals one at every nonzero scalar point. Since the omitted singleton has zero Lebesgue measure, it equals one almost everywhere. On the entire compact sublevel F≤3 the classical radial Hessian expression (x+1)²F''(x) lies between zero and three almost everywhere. This upper bound follows from the actual objective gap inequality, not an assumed compact radius.

Nevertheless the exact radial central difference at the nonoptimal kink x=0, using star=−1, is t²+2|t|. It is not O(t²). More directly, `shifted_no_radial_secant_bounds` disproves the actual RS predicate on the compact sublevel F≤3: actual differentiable descending crossing pairs in the fixed positive band η=1/4 have a radial numerator bounded away from zero and actual curvature tending to zero. Both actual gradients and all band and ordering conditions are supplied from previously checked formulas. No eligibility shortcut or assumed gradient values is used.

`singular_curvature_counterexample` packages the actual strong convexity, attained unique minimum, compact sublevel, almost-everywhere bound and failure of RS. This closes the source logical warning that bounded classical radial Hessian almost everywhere does not suffice: the kink contributes singular radial curvature. It is not a failure of BFGS convergence; the earlier scalar theorem already proves convergence of every admissible run on this objective.

Main build: `radial_continuation_build.log`. Complete importing axiom audit: `RadialSingularCurvatureAudit.lean`, `radial_singular_curvature_axioms.log` and `radial_singular_curvature_validation.log`. All 10 declarations depend only on propext, Classical.choice and Quot.sound. The original scratch source/evidence remains preserved.
