# Sixth report milestone: structural source closure

The nine new exact propositions in `ReportStructuresTargets.lean` are inhabited
without additional premises in `ReportStructuresEndToEnd.lean`. Their definitions
and inhabitants are printed/checked by `Audit.lean`, which also traverses every
theorem in the compiled project environment. The full release audit, source
hash validation and report register are the authority for verified status.

- `maxAffineThreshold` uses the actual finite maximum and literal extended-real
  infimum over inactive closed active regions. Empty regions contribute infinity.
  Attainment, strict separation above the unique minimum, local active-slope
  identity and the explicit gap/radius formula are derived. It applies after
  any accepted finite prefix with the current full-BFGS matrix. See
  `MAX_AFFINE_BASIN_STATEMENT_REVIEW.md` and the independent peer review.
- `mixedLinearPowers` includes arbitrary finite nonnegative convex degree-one
  gauges, real exponents at least one, arbitrary linear maps and varying
  component dimensions. The uniform basin is derived before every run; no
  component coercivity, component differentiability, or limiting metric is
  assumed. Actual radial derivative and Taylor bounds are proved. See
  `POWERED_GAUGE_STATEMENT_REVIEW.md`.
- `polyhedralBasin` derives local full-BFGS convergence from actual finite
  affine-inequality cells and local C1,1 extensions on their individual open
  domains. Only the full objective is required convex. The stronger underlying
  proof permits lower-dimensional closed convex cells and identifies their
  actual one-sided radial derivatives. `smoothPLQBasin` derives the required
  regularity from actual quadratic coefficients. See
  `CONVEX_CELL_RADIAL_STATEMENT_REVIEW.md` and `R_FAMILY_COVERAGE_MAP.md`.
- `recurrentLowRank` proves that the actual recurrent slope span of dimension
  at most two and a finite objective-value limit imply full ambient iterate
  convergence and zero limiting value. It does not assume bounded iterates,
  bounded gaps between independent transitions, or any matrix limit. Exact
  dependent-block control, recurrence selection and current-metric lifting are
  proved. `relativeInteriorClass` identifies the source class exactly with
  nonnegative finite maxima having a linear zero fiber. H energy budgets and
  the actual seminorm/gauge consequences are separately exported. See
  `H_LOW_RANK_VERIFICATION.md`.
- `parabolicPruning` derives the actual pruned family, preservation of the
  entire objective, strictly ordered slopes and breakpoints, positive envelope
  values and exact adjacent calibration. `parabolicPrintedField` verifies the
  literal printed piecewise scale's matrix field on every compact positive
  band. Its normalization, continuity and explicit accepted-pair identities
  are proved. See `MODULE_Q_SOURCE_MAP.md`; these close Q's previously tracked
  source-description obligations without changing its mathematical statement.
- `fivePieceObstruction` constructs actual SPD starting matrices and actual
  gradients in every neighborhood of the unique minimizer, and excludes all
  positive differentiable trials satisfying ordinary Armijo--weak-Wolfe with
  the source constants. Coercivity, unique minimizer, search direction and all
  three ray regions are independently proved. See the statement and peer
  reviews `FIVE_PIECE_OBSTRUCTION_*_REVIEW.md`. This is finite inability to
  continue, not an infinite-run convergence counterexample.

The 24 scoped A barycentric declarations are also imported and audited. They
prove exact Gram-inverse/augmented-system geometry and its local stability.
Their application to an actual finite smooth-max subdifferential remains
explicitly conditional pending that separate bridge; see
`A_BARYCENTRIC_VERIFICATION.md`. They do not certify Module A's main application.

No original research source was changed. Q's internal mathematical claims are
closed. H's internal theorems are closed, while its references to an earlier
three-gradient example and the external two-piece finite-termination theorem
remain separately recorded source cross-references. The rank-at-least-three
zero-value iterate question is an explicit open question, not a theorem.
Remaining F/R concrete applications and matrix/line-search constructions,
C/U/A, D/L, source interpretations and synthesis are still obligations.
