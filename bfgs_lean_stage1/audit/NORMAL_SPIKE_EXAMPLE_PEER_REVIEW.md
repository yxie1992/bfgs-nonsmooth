# Independent review: U.20, U.21 and failure of RS

Reviewed all eight files `NormalSpikeObjective`, `NormalSpikeGradient`,
`NormalSpikeRadialBound`, `NormalSpikeSamples`, `NormalSpikeSeparation`,
`NormalSpikeInterface`, `NormalSpikeHessian`, and `NormalSpikeExampleTargets`
in `audit/scratch/normal_spike`, against Module U's explicit example following
U.18--U.19. The reviewed snapshot is the eight hashes in
`example_source_hashes.json`. The scalar infinite-series construction has its
own preceding independent review.

Result: no unresolved mathematical or statement defect in this scope. The
structural check was independently rerun: 66 explicit declarations, standard
transitive axioms only, four exact targets, eight unchanged hashes. The
compiler, axiom and exact-target records are `example_build.log`,
`example_axioms.log`, `example_contracts.log`, and `example_validation.log`.

- The objective is exactly the source quadratic plus `|v|+r(v)`. The final
  coordinate split is proved for `Fin.cons v u`; dimensions `n+2` cover every
  finite dimension at least two. One Euclidean unit normal is used for the
  coordinate-free intermediate results. The Euclidean strong-convexity
  constant is actually one. Coercivity, all compact sublevels, the attained
  zero value and uniqueness of the zero minimizer are derived.
- Global full-BFGS convergence invokes the checked full-strong composite
  theorem with the actual objective, actual normal and actual smooth/scalar
  decomposition. Its local C1,1 assumptions are proved from the scalar's
  actual C3 regularity off zero and the quadratic. The final result quantifies
  over every actual admissible full-BFGS run. It adds no restriction on initial
  SPD coupling, matrix convergence, iterates, step lengths or frame budgets.
- Differentiability holds exactly off the normal hyperplane. At the
  hyperplane, the two distinct actual supports `x+a` and `x-a` contradict
  differentiability. Every actual support has the stated tangential
  projection, and the coordinate tangential projection is actually
  1-Lipschitz in the finite-Pi norm as well. No continuity of an arbitrarily
  selected full gradient at the interface is assumed.
- The positive-side actual gradient and its radial difference derivative are
  proved by differentiation. The Hessian target uses `RadialHessian.matrix`,
  defined from the actual second Fréchet derivative. The separate actual
  second derivative along the inward ray and the checked bilinear-matrix
  identity give the source peak formula. The generic radial formula holds at
  every positive-normal point; the scalar tangential sample in the final
  target supplies a sufficient fixed tangential direction in every dimension
  for the unbounded-curvature argument.
- RS failure has the required order of quantifiers. For a fixed positive
  tangential height `u`, the positive band is `η=u^2/8`, chosen before the
  alleged RS constant. All sufficiently late peaks lie in the chosen positive
  sublevel. Every inward contraction with `0<t≤1/2` remains in that sublevel
  and the same positive band, has differentiable endpoints and decreasing
  objective order, and has strictly positive actual secant curvature. The
  exact numerator/denominator identities turn the RS inequality into a bound
  on actual radial curvature. Its one-sided limit is incompatible with the
  diverging peaks. The final neighborhood theorem uses a derived sublevel
  basin inside the arbitrary neighborhood, rather than presuming such a
  neighborhood is radial or convex.

The source's appeal to an inward-smoothness equivalence is replaced here by a
direct RS contradiction on actual ordered endpoint pairs. This is a valid
proof-route change with the same conclusion. The scalar peak formulas and
noncontinuity are not treated as substitutes for actual derivative existence.

The variable-jump example U.7.2, rational-query corollaries, and numerical
BFGS experiments are outside these eight files and this review. Their absence
does not weaken any of the four reviewed exact targets. Main integration must
still rebuild and include these files in a subsequent whole-project audit.
