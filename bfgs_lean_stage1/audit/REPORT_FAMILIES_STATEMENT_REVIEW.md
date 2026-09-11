# Fifth report milestone: reviewed target scope

The eight exact contracts in `ReportFamiliesTargets.lean` are inhabited in
`ReportFamiliesEndToEnd.lean` with no additional hypotheses. Root `Audit.lean`
prints these definitions, checks their inhabitants and traverses all theorem
dependencies in the compiled project environment.

- `parabolicCertificate` constructs the literal θ²rrᵀ field on every compact
  positive band of the original arbitrary finite family. `parabolicConvergence`
  proves actual full-BFGS objective and iterate convergence. See
  `PARABOLIC_CONVERGENCE_STATEMENT_REVIEW.md` and the independent envelope and
  transport reviews. Uniform thresholds and all calibration data are derived.
- `transformedGaugeConvergence` has precisely the source F:transform hypotheses:
  a finite convex coercive degree-one gauge and a scalar transform continuous,
  convex and strictly increasing on [0,∞), zero at zero, C² with positive
  derivative on (0,∞). The inverse and Θ' formula are separately proved, as are
  actual endpoint gauge differentiability and the exact correction coefficient.
  The real extension below zero plays no role. See
  `TRANSFORMED_GAUGE_STATEMENT_REVIEW.md`.
- `relativeInteriorConvergence` and `recurrentRelativeInterior` derive whole
  accepted-sequence convergence to a minimizer under the respective actual
  finite slope-set relative-interior condition. Coordinates are derived; the
  targets do not add a basis or a projected-limit premise. The more informative
  source metric-fiber formula and unique metric-minimizer characterization are
  exported separately and explicitly checked in `Audit.lean`. The recurrent
  proof preserves only actual accepted values/derivatives when restricting the
  objective; it does not assert false global equality with the original finite
  maximum. See `H_RELATIVE_INTERIOR_VERIFICATION.md`.

- `parabolicEligibleSeparation` chooses a positive band before every small-decrease
  threshold and candidate radial bound, then derives an actual eligible pair
  and its SPD unit-step BFGS witness. `parabolicNonnecessity` combines every-run
  convergence with RS failure in every neighborhood. Printed-scale bounds and
  pair correction/log identities are separately proved. See
  `PARABOLIC_EXAMPLE_STATEMENT_REVIEW.md`; the all-c1 extension is distinguished
  from the printed pair's exact c1≤2/3 range.
- `accessibleActiveSeparation` packages an actual constant-I certificate and
  genuine limiting gradients at a nonoptimal kink whose full-active tangent
  projections vanish. The explicit `(c1,c2)=(1/8,1/4)` avoids accessible small
  kink crossings. This strengthens the G.4 correction from an algebraic model
  to an actual objective counterexample; see `G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md`.

Independent source review confirms no new convergence assumption or algorithm
modification. The source description remains provisional outside these exports.
The entire report, H.7.4, the remaining R/F applications, C/U/A, D/L and synthesis
are not claimed verified by this milestone. Q ordered-envelope bookkeeping,
example scale identities and H.8 class characterizations are tracked separately
where not covered by a specific audited declaration.
