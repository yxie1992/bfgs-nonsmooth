# First entire-report tranche: statement and dependency review

The canonical research sources are preserved. The exact five new proposition
exports are in `ReportCoreTargets.lean`; their inhabitants are in
`ReportCoreEndToEnd.lean`. `Audit.lean` prints their definitions and the underlying
run/certificate definitions, and enumerates every transitive theorem dependency.
This is a collaborating-agent review, not external mathematical peer review.

## Reviewed objective-level conclusions

- `transportedCertificateConvergence`: Module T's primary theorem with the
  actual PSD field, actual Euclidean step projector, positive nonempty bands,
  and small eligible pairs. Field continuity, boundedness and positive
  definiteness are not assumed. Accepted-pair eligibility and the Hessian trace
  recurrence are derived from ordinary full BFGS. Optimal values, Euclidean
  distance to all minimizers, and the uniqueness upgrade are all included.
- `homogeneousDichotomy`: H.A's unrestricted finite-dimensional value dichotomy
  for finite convex degree-one objectives. Neither a finite slope alphabet nor
  bounded iterates, displacements, lengths or matrices is assumed. Euler and
  support-at-zero derive a global gradient bound. The finite-value argument
  excludes negative as well as positive nonzero limits. Separate checked
  consequences cover bounded-below objectives, coercivity, and nonpositive-value
  escape.
- `scalarMetricConvergence`: G's scalar theorem with an arbitrary positive
  metric sequence. `ScalarMetricRun` has no metric-update condition. An assumed
  persistent positive gap derives summable step distances and a nonoptimal
  point limit; weak Wolfe then forces gradient contraction, contradicting the
  derived gradient lower bound. That point limit is a contradiction argument,
  not an assumption in the theorem.
- `scalarBFGSConvergence`: exact dimension-one specialization of the actual
  objective and matrix run. The coordinate embedding and derivative/step/Wolfe
  identities are checked; all scalar metrics are proved positive from the
  actual propagated SPD matrices.
- `radialCertificateConvergence`: the positive-band RS sufficient condition
  underlying R's applications. The hypothesis contains actual ordered
  differentiable objective endpoint pairs and positive secant curvature. The
  actual reference-correction bound is derived from it, then Module M supplies
  convergence. The conclusion includes actual Euclidean solution-set distance.

## Shared conclusions and representations

Compact initial sublevels yield an attained global minimum. Lower-bounded actual
accepted values yield a real limit by Armijo monotonicity, without claiming its
optimality. On a compact containing set, optimal values imply distance to the
whole solution set tends to zero; uniqueness is unnecessary. A zero actual
gradient certifies a global minimum, justifying successful termination outside
the infinite nonzero-gradient run model.

The coordinate model `Vec n` has mathlib's finite-Pi norm. The report targets
explicitly use `EuclideanSpace ℝ (Fin n)` for distance: `euclideanVector` maps
coordinates unchanged, and `euclideanSolutionDistance` takes the metric infimum
to the image of the actual argmin. The continuous-coordinate-map compactness
proof checks this bridge without relying on an informal norm equivalence.

The radial supporting-plane and intercept identities are proved algebraically.
The scalar conversions RS-to-intercept and converse retain the exact source
constant `2C+2Tmax`. These conversions alone do not prove the full objective
RS/intercept equivalence or the inward-radial theorem; the uniform curvature
bound and those complete applications remain obligations.

## Disclosed proof choices and scope

T and H use Module M's stronger summable-budget growth theorem where the source
uses qualitative reciprocal growth. Both derive the required summability from
exactly their original compact/lower-value hypotheses. T's unused `b>F*`
assumption is dropped in a proved generalization; no conclusion is weakened.
Empty RS bands impose a vacuous universal pair condition, so a constant can
always be chosen there.

This tranche does not verify all of T, H, G or R. Their detailed inventories and
`REPORT_STATUS.json` retain secondary claims as open. In particular: certificate
normalization/geometric obstructions, T local/gauge/affine variants, H recurrent
slope and low-rank iterate theorems, R inward smoothness equivalence and concrete
families, and all later geometric/counterexample modules remain separate work.

Independent reviews: `T_CORE_PEER_REVIEW.md`, `H_CORE_PEER_REVIEW.md`, and
`COMPACT_RADIAL_PEER_REVIEW.md`. The full current compiler and axiom evidence is
`build.log`, `axioms.log`, `declarations.json`, and `report_core_check.log`.
