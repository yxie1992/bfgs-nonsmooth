# Compact and radial convergence peer review

Reviewed `CompactConvergence.lean`, `RadialCertificate.lean`,
`RadialConvergence.lean`, and the corresponding statements in
`ReportCoreTargets.lean` against Module R's setup and (R.RS), its
supporting-plane identities (R.SP), and the shared compactness conclusions.
The original report sources were not edited.

## Result

No remaining mathematical hypothesis gap was found in the displayed compact
or radial convergence declarations. Their conclusion is optimal objective
values and distance to the entire minimizer set; convergence to a particular
point additionally requires uniqueness. They do not assert unconditional
convergence of all full-BFGS runs or convergence of BFGS matrices.

## Compactness and nonunique minimizers

- `argmin F` is the set of global minimizers over the entire ambient space.
- `exists_global_minimum_of_compact_sublevel` first minimizes on the nonempty
  actual initial sublevel, then proves the resulting point is a global minimum:
  every point outside that sublevel has strictly larger value than the initial
  iterate. It does not assume existence of a global minimum.
- `objective_value_limit_of_lower_bound` derives a finite real limit from the
  Armijo monotonicity theorem and a displayed lower bound. This limit is not
  assumed optimal. Compact initial sublevels supply that lower bound.
- The generic distance theorem requires only continuity, containment in a
  compact set, and values tending to an attained global minimum. Every cluster
  point then belongs to `argmin F`. Neither uniqueness nor connectedness nor
  differentiability of minimizers is used.
- The mapped-distance version proves the same claim for the continuous image
  of the actual minimizer set; it does not replace that set by an unrelated
  comparison set. `euclideanVector` is the standard finite-coordinate L2
  realization, and `euclideanSolutionDistance` uses its genuine Euclidean
  metric. The final report targets explicitly use this Euclidean distance.
  The earlier plain `Metric.infDist` wrapper uses the finite-Pi metric, which
  is valid but is not advertised as a quantitative Euclidean distance identity.
- A zero actual gradient implies a global minimum by convexity, independently
  of the infinite-run model's nonzero-gradient condition.

## Radial certificate and actual BFGS bridge

- `HasRadialSecantBounds` retains the exact ordered endpoint conditions from
  (R.RS): both endpoints lie in the displayed set, both have actual derivatives,
  `F star + eta <= F z <= F x`, and actual secant curvature is positive. The
  constant may depend on the positive band. No line-search eligibility or
  assumed metric condition is substituted for this objective hypothesis.
- No sign condition is silently imposed on the existential constant. Empty
  bands are vacuous; on any tested positive-curvature pair its required square
  bound already controls its sign. The cumulative estimate safely enlarges
  it to `max C 0`.
- The supporting errors use only the derivative at their base endpoint. The
  secant-curvature decomposition and optimizer-intercept identity have the
  source's signs and endpoint order. The two scalar conversion lemmas give
  the exact constant `2*C + 2*Tmax`, with the required explicit hypotheses
  `0 <= D <= T <= Tmax`.
- `radial_correction_bound` identifies the run's actual displacement and
  gradient difference with those endpoint quantities. Its denominator is the
  actual curvature, whose positivity is already derived from the run's Wolfe
  condition and inductively proved positive definiteness. The correction is
  not an independent scalar sequence or an extra budget hypothesis.
- In the nonoptimal-limit case, the gap `ell - F star` selects one positive
  band containing all iterates. RS then bounds every actual correction;
  compactness supplies bounded actual gradients; the existing verified
  full-BFGS energy criterion forces optimal values. No matrix or iterate limit
  is assumed. The sublevel wrapper derives containment by Armijo.
- The source assumes `b > F star`. Omitting that redundant hypothesis in the
  accepted-run sublevel wrapper strengthens the statement without changing its
  reasoning: membership of the actual initial iterate already ensures a
  nonempty containing sublevel, while global minimality controls its values.

## Scope still outside these files

The scalar (RS)/(SP) constant-conversion lemmas are not yet an exported
objective-level equivalence with a derived uniform curvature bound. The inward
radial smoothness equivalence (R.IR), nondifferentiable inner-endpoint
approximation, central differences, and the objective families in later
sections of Module R remain separate obligations. These files do not verify
those claims merely by verifying the radial convergence criterion.

## Compiler verification

An initial reversed order-limit API call in `radial_certificate_values` was
reported and corrected by the owning agent from `le_of_tendsto` to
`ge_of_tendsto`; it is resolved in the reviewed file. The independent command

```sh
source scripts/env.sh
lake build BfgsVerification.CompactConvergence BfgsVerification.RadialCertificate BfgsVerification.RadialConvergence BfgsVerification.ReportCoreTargets
```

completed successfully. The actual output is preserved in
`audit/compact_radial_peer_build.log`. Only existing dependency linter warnings
were replayed. The parent task owns full-project transitive axiom auditing and
the global status register; this peer review does not stand in for that audit.
