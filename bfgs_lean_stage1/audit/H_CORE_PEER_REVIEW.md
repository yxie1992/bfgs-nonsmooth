# Independent review of the Module H.A core

Reviewed source H.A and H.5 against `Homogeneous.lean`, `HomogeneousDichotomy.lean`, and `HomogeneousConsequences.lean`. This is an independent collaborating-agent review, not external mathematical peer review. No reviewed source files were edited.

**Finding: no mathematical or theorem-statement defect identified in the H.A core.**

* `PositiveDegreeOne` is the actual equality `F(t • x)=t F(x)` for every nonnegative real scale. `AdmissibleBFGSRun` supplies a real-valued finite convex objective, actual gradients at accepted points, ordinary full updates, initial SPD, positive lengths, nonzero gradients, and fixed Armijo–weak-Wolfe. No finite max representation or finite gradient alphabet is imposed.
* The global gradient bound is derived: Euler's identity and supporting-plane linearity move every supporting vector to the subdifferential at zero, and the previously checked finite-convex compact bound is applied to `{0}`. No iterate boundedness or compact accepted sublevel is assumed.
* The exact reference-zero Hessian energy and homogeneous potential inequalities use the actual proved Hessian update. The correction is bounded by `h_k`, then by actual predicted decrease; it is not an independently assumed scalar recurrence.
* `homogeneous_finite_value_limit_zero` takes a **real** limiting value and excludes both positive and negative nonzero limits by the absolute-value lower bound `|L|/2` on a shifted actual run. The shift's SPD and gradient properties are derived. Summability and reciprocal growth follow from the actual finite-value run theorem; no matrix convergence or assumed summability is added.
* `homogeneous_value_dichotomy` derives a finite limit from monotonicity when the actual value sequence is lower bounded, and derives convergence to `atBot` otherwise. Its input adds homogeneity only. The escape branch is not restricted to pre-assumed unbounded iterates.
* Strict positivity at every point on the finite branch follows from strict accepted descent and the next value's nonnegative limit bound. Consequently a single nonpositive accepted value selects escape, exactly as H.A states.
* The bounded-below consequence proves nonnegativity everywhere and minimum value zero at the origin. The coercive consequence derives boundedness of the zero sublevel, positivity away from zero, uniqueness, and iterate convergence. Coercivity is explicit `Tendsto F (cocompact (Vec n)) atTop`, with no bounded-run premise.
* The finite-Pi norm in the coordinate model has the standard finite-dimensional topology. Coercivity, boundedness, and convergence agree with their Euclidean formulations; no quantitative Euclidean norm identity is required for these conclusions.

The finite-limit proof uses the already verified stronger summable-budget reciprocal theorem, rather than duplicating H.5's original arithmetic-mean argument. It derives the required summability under precisely the finite-value assumption, so this is a proof-route change rather than a changed theorem.

Verification evidence: an independent pinned `lake build BfgsVerification.HomogeneousConsequences` succeeded. Direct transitive axiom checks for finite-limit zero, the unconditional dichotomy, finite-branch positivity, nonpositive escape, bounded-below convergence, and coercive iterate convergence all returned only `propext`, `Classical.choice`, and `Quot.sound`. Commands and outputs are in `audit/H_CORE_PEER_BUILD.log`.

This review does **not** certify H.B/H.C, recurrent-gradient affine geometry, planar iterate classification, or the all-dimensional noncompact zero-branch iterate question. Those require their separately recorded proofs.
