# Module U inventory and implementation boundaries

Source read in full: `BFGS_MASTER_REPORT_LaTeX/report/chapters/U.tex`. This register distinguishes the checked principal U.1/U.2 tranche from secondary source obligations. The principal tranche is scoped-audited separately before seventh-release integration; it is not a claim that every assertion in Module U is verified.

## Exact primary results

1. U.1: finite convex F, unique minimizer on a fixed hyperplane, compact initial sublevel, positive Euclidean strong convexity on an open convex neighborhood, all actual subgradients share one Lipschitz tangential projection, local C1,1 away from the hyperplane. Derive convergence of every actual infinite admissible full-BFGS run, for arbitrary initial SPD metric. The exceptional plane can contain differentiable points and failures of local C1,1. Derive a local basin independent of the initial SPD matrix and valid fixed line-search constants.
2. U.2: the same structure for a closed set E of parallel exceptional scalar levels, every exceptional point genuinely nondifferentiable. Derive an actual affine-critical cluster point. Adding affine-critical correctness yields value convergence, and uniqueness yields point convergence. No finite number of interfaces or cluster points may be assumed.
3. U.1.1/U.6: the actual composite family smooth convex psi plus scalar convex h, with tangential strong convexity only, unique minimizer on the plane, compact initial sublevel, and strictly convex positive sublevels. Derive tangential displacement and secant bounds, full steps tending to zero, and convergence. This is weaker than full strong convexity and must remain a separate statement.

## Proof-chain coverage

- **Checked:** U.10: strong supporting inequality, strong gradient monotonicity, summable squared displacement, and actual steps tending to zero. Use Euclidean `sqNorm`, not the default finite-Pi norm in mathlib's `StrongConvexOn`. An exact coordinate definition is convexity of `F - (mu/2)*sqNorm`; prove the supporting inequalities from it.
- **U.11 checked; composite U.17 remains:** derive tangential secant bounds from the actual gradient and common projection field. Composite U.17 uses the checked `CenteredCocoercivity.exists_cocoercivity_constant_on_compact` and scalar supporting monotonicity.
- The compact cluster set and eventual neighborhood containment are derived for the actual trajectory. Existing CompactConvergence gives the objective limit and point/value conclusions; StrictContours gives step convergence under strict contours. Do not assume a chosen iterate limit.
- On genuinely exceptional points, compact convex nonempty actual subdifferentials and the singleton/differentiability criterion are now checked in the four-file Supports tranche. A common codimension-one tangential projection plus derived distinct supports now gives the affine-zero iff A=0 statement; the literal full affine-line/compact-segment description remains tracked below.
- **Checked:** derive a Lipschitz scalar cutoff from positive separation between the compact image of tangential-zero cluster points and the closed exceptional level set. Include empty exceptional-set and empty tangential-zero-set cases.
- **Checked:** U.12: use an actual orthonormal-column basis of the normal complement, available via `FrameNorms.orthonormal_matrix_for_subspace`; derive projection identities. The frame `[U,tau*a]` has unrestricted tangential dimension and no rank premise when the cutoff vanishes.
- **Checked:** derive uniform late visibility on the entire cluster set, using continuity of the cutoff-masked actual gradient. A discontinuous raw gradient selector at the exceptional set cannot be used as if globally continuous.
- **Checked:** U.13: compactness and local smooth charts away from the exceptional set yield one secant constant for sufficiently close accepted pairs. Existing local uniform Lipschitz and cocoercivity lemmas provide the analytic ingredients; the strip/cutoff coverage and late accepted-endpoint quantifiers are now derived in `FixedNormalSmoothStrip`. For full strong convexity, the proof uses local derivative Lipschitzness and strong curvature directly.
- **Checked:** U.14/U.15: exact matrix transport identity with T=I, zero-safe divided-difference beta, tangential residual and derived Frobenius estimate. The arbitrary-tail `ResidualFrames.residual_frames_on_tail_incompatible` consumes these bounds and internally derives the actual Hessian trace recurrence and reciprocal-growth contradiction. Final U statements must not assume these frame hypotheses.

## Explicit examples and source corrections

- U.18/U.19: actual locally finite spike series k and integral r, all masses, global C1/convexity, C3 off zero, near-zero upper bounds, second derivative at zero, and divergent peak curvature.
- U.20/U.21: actual all-dimensional strongly convex/coercive objective and its full-BFGS convergence, with exact radial-secant failure in every optimizer neighborhood via the checked RS/inward equivalence and second-order limit. No assumed spike oracle may replace the series.
- U.7.1: exact infinite-tail mass/moment formulas, partial-bump polynomial integrals, and peak values. Numerical logs are experiments only.
- U.7.2: actual variable-jump model, strong convexity constant, common Lipschitz tangential field, local convergence, and radial separation. The source's claim that the objective does not admit a smooth-plus-univariate splitting requires **c != 0**. The printed range `norm c < 1` includes c=0, where such a splitting explicitly exists. Record the non-additive statement only under c != 0; the convergence statement itself still permits c=0. Original research source remains unchanged.

## Current status

The principal U.1/U.2 proofs and local/source wrappers compile in eleven main `FixedNormal*.lean` modules. They contain 80 explicit declarations, with five exact target definitions/inhabitants. Actual transitive axiom and exact-type audit evidence is recorded in `FIXED_NORMAL_PRINCIPAL_*` artifacts and `fixed_normal_principal_validation.log`; the independent review is `FIXED_NORMAL_PRINCIPAL_PEER_REVIEW.md`.

| Source claim | Checked declaration / scope |
| --- | --- |
| U.1 global fixed hyperplane | `AdmissibleBFGSRun.fixed_normal_hyperplane_convergence` |
| U.1 local basin, uniform over initialization and fixed valid line search | `FixedNormal.local_hyperplane_convergence_basin` |
| U.2 arbitrary closed parallel interfaces | `AdmissibleBFGSRun.parallel_interfaces_affineCritical_cluster` |
| U.2 specified compact trapping sublevel | `parallel_interfaces_affineCritical_cluster_on_sublevel` |
| U.2 affine-correctness consequence | `parallel_interfaces_convergence_of_affine_correctness` |
| U.2 local affine-correctness basin | `FixedNormal.local_parallel_interfaces_convergence_basin` |
| U.10 actual strong inequalities, summability and vanishing steps | `FixedNormalStrongConvex.lean` |
| U.11 actual tangential secant and Hessian trace budget | `FixedNormalRunBounds.lean` |
| Entire-cluster cutoff and visibility, including empty cases | `FixedNormalCutoff.lean`, `FixedNormalVisibility.lean` |
| U.13 eventual actual smooth-strip secant estimate | `FixedNormalSmoothStrip.lean`; local Lipschitz plus full strong curvature derives the required constant |
| U.12/U.14/U.15 actual basis, frame pairing, transport and residual | `FixedNormalProjection.lean`, `FixedNormalFrame.lean`, `FixedNormalRunBounds.lean` |
| U.2 actual nonsmooth affine-zero iff tangent-zero | `FixedNormal.affine_critical_iff_tangent_zero` |
| Literal nontrivial compact segment and full affine-line equality | Remaining source-description obligation; sufficient distinct-support/affine-zero statements are checked |
| U.1.1 composite representation and weaker U.6 tangential curvature | Remaining objective-family/analytic obligation |
| U.18–U.21 actual spike series, derivative bounds and radial failure | Remaining exact-series obligation |
| U.7.1 exact oracle formulas | Remaining exact-integration obligation |
| U.7.2 variable jump example and non-additive claim | Remaining example obligation; non-additive assertion requires `c != 0` |

The source review `FIXED_NORMAL_PRINCIPAL_STATEMENT_REVIEW.md` records exact assumptions and the internal derivation of all frame/hierarchy inputs. No iterate or matrix convergence, assumed hierarchy, or algorithm modification is used. The historical core audit is retained as a narrower preliminary verification record, superseded for primary convergence coverage by the principal audit. Original research sources remain unchanged.
