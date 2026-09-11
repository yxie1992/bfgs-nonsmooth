# Seventh report milestone: actual analytic models and exact seed

The 17 new exact targets are twelve propositions in ReportAnalyticTargets and
five in FixedNormalTargets, inhabited in their corresponding EndToEnd modules.
Audit.lean prints the transparent targets, checks their inhabitants and audits
every theorem in the compiled project environment, including auxiliaries.
The full release audit and source hashes are authoritative for final status.

- Actual finite-max subdifferentials equal the convex hull of actual active
  gradients. The full objective is convex; branches need only be locally
  differentiable and may be nonconvex. Inactive original branches are removed
  by a proved neighborhood argument before the nondegenerate positive-weight
  affine-critical correctness theorem is applied. This discharges the earlier
  conditional barycentric application. See CONVEX_SUBDIFFERENTIAL_STATEMENT_REVIEW.
- Actual minimum-norm affine projection/equal-rate geometry and compact cluster
  reduction are verified. The literal strongly convex rank-loss example has
  actual affine-subdifferential distances, global affine correctness and the
  positive limiting objective gap. It is not a bad BFGS run. The source's local
  lower-semicontinuity deduction and semialgebraic finite-value theorem remain
  separately tracked. See A_CANONICAL_RANK_LOSS_VERIFICATION.
- The finite-C2-max radial branch-compatibility theorem derives actual inward
  and radial bounds and a uniform local BFGS basin. Its compact version permits
  nonunique minimizers. The exact linear central obstruction is checked; the
  source's full J|t|+O(t^2) formula is still a separate retained detail. See
  FINITE_MAX_RADIAL_STATEMENT_REVIEW.
- Affine Euclidean group residuals are split using their actual optimal
  residuals. Smoothness of each nonzero residual is derived, and the literal
  matrix wrapper permits overlapping/singular rectangular maps and varying
  dimensions. See EUCLIDEAN_RESIDUAL_STATEMENT_REVIEW. Actual full-gradient
  matching at adjacent full-dimensional cells is in CellDerivativeMatching.
- The literal u^2+|v| actual admissible run proves the arbitrary unexcited
  tangential inverse entry persists, with exact iterates, updates, acceptance
  ratios and limits. No convergence is used as a premise. Finite full-space
  nondifferentiability along a bounded-below descent ray gives an actual strict
  differentiable Armijo/weak-Wolfe step. That existence theorem uses a proved
  tilted-minimum interval; it does not assert arbitrary-oracle termination.
  See UNEXCITED_METRIC and FINITE_RAY_LINE_SEARCH statement/peer reviews.
- The literal parabolic and shifted nuclear-norm examples prove fixed-positive-
  band RS failure in every neighborhood, with actual objectives, derivatives,
  descending pairs and exact quotients. The nuclear model uses actual Hermitian
  eigenvalues and exact Frobenius coordinates. These are certificate failures,
  not bad BFGS trajectories; Module Q additionally proves convergence for the
  parabolic objective. See PARABOLIC_RADIAL_BOUNDARY_STATEMENT_REVIEW and
  NUCLEAR_SPECTRAL_STATEMENT_REVIEW.
- U.1/U.2 and their uniform local basins derive cutoff, whole-cluster visibility,
  smooth-strip bounds and exact residual-frame budgets from the actual objective
  and run. U.2 allows an arbitrary closed interface set. Genuine nonsmoothness
  is required there; U.1 allows smooth exceptional points. Neither assumes
  iterate/matrix convergence. The weaker tangential-only extension and explicit
  series/variable-jump examples remain open. See FIXED_NORMAL_PRINCIPAL reviews.
- D/L's exact unique algebraic root, factor/ratio bounds, actual Jacobian inverse,
  residual and strict supremum certificate are now checked. Generated rational
  candidates are verified inside the kernel. Later BFGS closure, deterministic
  search and dynamical embeddings remain open. See ALGEBRAIC_SEED reviews.

The C algebra/actual scalar-energy core is also audited, with endpoint field
estimates explicitly conditional. The actual objective construction is ongoing
in scratch and is not claimed by this milestone. Original research sources are
preserved. The entire-report flag remains false.
