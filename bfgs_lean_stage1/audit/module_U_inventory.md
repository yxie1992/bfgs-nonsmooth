Current source reconciliation at milestone14: **verified with the documented nonzero-jump-parameter correction**.
See [RU_SOURCE_RECONCILIATION.md](RU_SOURCE_RECONCILIATION.md) and REPORT_STATUS.json.
Chronological pending entries below are historical, not current status.

# Module U inventory and implementation boundaries

Source read in full: `BFGS_MASTER_REPORT_LaTeX/report/chapters/U.tex`. This register distinguishes the checked principal U.1/U.2 tranche from secondary source obligations. The principal U.1/U.2 tranche was included in seventh release f820c46. The subsequent composite/literal-geometry tranche has separate scoped compiler, exact-target and axiom evidence; it is not a claim that every assertion in Module U is verified.

## Exact primary results

1. U.1: finite convex F, unique minimizer on a fixed hyperplane, compact initial sublevel, positive Euclidean strong convexity on an open convex neighborhood, all actual subgradients share one Lipschitz tangential projection, local C1,1 away from the hyperplane. Derive convergence of every actual infinite admissible full-BFGS run, for arbitrary initial SPD metric. The exceptional plane can contain differentiable points and failures of local C1,1. Derive a local basin independent of the initial SPD matrix and valid fixed line-search constants.
2. U.2: the same structure for a closed set E of parallel exceptional scalar levels, every exceptional point genuinely nondifferentiable. Derive an actual affine-critical cluster point. Adding affine-critical correctness yields value convergence, and uniqueness yields point convergence. No finite number of interfaces or cluster points may be assumed.
3. U.1.1/U.6: the actual composite family smooth convex psi plus scalar convex h, with tangential strong convexity only, unique minimizer on the plane, compact initial sublevel, and strictly convex positive sublevels. Derive tangential displacement and secant bounds, full steps tending to zero, and convergence. This is weaker than full strong convexity and must remain a separate statement.

## Proof-chain coverage

- **Checked:** U.10: strong supporting inequality, strong gradient monotonicity, summable squared displacement, and actual steps tending to zero. Use Euclidean `sqNorm`, not the default finite-Pi norm in mathlib's `StrongConvexOn`. An exact coordinate definition is convexity of `F - (mu/2)*sqNorm`; prove the supporting inequalities from it.
- **Checked:** U.11/U.17: derive tangential secant bounds from the actual gradient and common projection field. Composite U.17 uses the checked `CenteredCocoercivity.exists_cocoercivity_constant_on_compact` and scalar supporting monotonicity.
- The compact cluster set and eventual neighborhood containment are derived for the actual trajectory. Existing CompactConvergence gives the objective limit and point/value conclusions; StrictContours gives step convergence under strict contours. Do not assume a chosen iterate limit.
- On genuinely exceptional points, compact convex nonempty actual subdifferentials and the singleton/differentiability criterion are now checked in the four-file Supports tranche. A common codimension-one tangential projection plus derived distinct supports now gives the affine-zero iff A=0 statement; the literal full affine-line/compact-segment description is now checked in `FixedNormalSegments`.
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
| Literal nontrivial compact segment and full affine-line equality | `FixedNormal.nonsmooth_subdifferential_parallel_segment` |
| U.1.1 fully coupled strongly convex composite family | `AdmissibleBFGSRun.strongly_convex_composite_convergence`; full strong convexity concerns F, not psi |
| U.1.1 local composite basin | `FixedNormal.local_strongly_convex_composite_basin` |
| U.6 weaker tangential curvature | `AdmissibleBFGSRun.tangential_composite_convergence`, with strict convexity only for relevant positive sublevels |
| U.6 local basin | `FixedNormal.local_tangential_composite_basin`, uniform over SPD initialization and valid fixed line search |
| U.16 projected supporting and displacement inequality | `FixedNormalTangentialStrong.lean` |
| U.17 actual scalar/smooth split and tangential secant | `FixedNormalCompositeCalculus.lean` |
| Derived composite off-interface local C1,1 | `FixedNormalCompositeSmooth.lean` |
| Cutoff-strip secant without full strong curvature | `FixedNormalCocoercivity.lean`, `FixedNormalTangentialFrames.lean` |
| U.18–U.21 actual spike series, derivative bounds and radial failure | Remaining exact-series obligation |
| U.7.1 exact oracle formulas | Remaining exact-integration obligation |
| U.7.2 variable jump example and non-additive claim | Remaining example obligation; non-additive assertion requires `c != 0` |

The source review `FIXED_NORMAL_PRINCIPAL_STATEMENT_REVIEW.md` records exact assumptions and the internal derivation of all frame/hierarchy inputs. No iterate or matrix convergence, assumed hierarchy, or algorithm modification is used. The historical core audit is retained as a narrower preliminary verification record, superseded for primary convergence coverage by the principal audit. Original research sources remain unchanged.

## Post-seventh composite tranche

Eleven additional main modules contain 39 explicit declarations and four exact target/inhabitant pairs. `FixedNormalCompositeEndToEnd` imports the global/local U.1.1 and U.6 proofs. `FixedNormalSegments` completes the literal exceptional-subdifferential description. The exact assumptions, separation of the two curvature alternatives, and derived full-BFGS proof chain are reviewed in `FIXED_NORMAL_COMPOSITE_STATEMENT_REVIEW.md`. Compiler/axiom/contract evidence is in `fixed_normal_composite_*` logs; independent review is `FIXED_NORMAL_COMPOSITE_PEER_REVIEW.md`. The historical prerequisite logs remain explicitly narrower in scope. The exact series/oracle/radial-failure/variable-jump assertions above remain obligations.


## Post-eighth scalar spike milestone

The actual scalar construction in U.18–U.19 is now main-built in nine `NormalSpike*.lean` modules (151 explicit declarations, one exact `SourceSpikePropertiesTarget`). The literal integral-defined function is proved equal to the actual infinite spline series; all convergence, regularity, total mass, disjoint-support, six-constant bounds, zero-endpoint second-derivative existence, exact peak formulas and unbounded/noncontinuous second derivative are derived. Closed-interval partial mass/moment formulas and complete geometric tails cover the printed U.7.1 identities. Main logs are `normal_spike_scalar_{build,axioms,contracts,validation}.log`; standard transitive axioms only. Independent review is `NORMAL_SPIKE_SCALAR_PEER_REVIEW.md`; the main validator confirms import-prefix-only differences from the reviewed snapshot.

The multidimensional U.20 actual-run convergence module is separately compiler-clean in scratch, but not yet part of this registered scalar scope. U.21 radial failure, all rational-query oracle evaluation, the complete variable-jump example and its non-additive assertion remain separate obligations. The main global status continues to describe the eighth release until parent integration.

## Post-eighth actual objective and executable oracle milestone

Nine more main modules now pass the pinned build and scoped audit: the eight-file U.20/U.21 tranche (66 declarations, four exact targets) and the one-file exact rational oracle (32 declarations, one exact target). The actual integral-defined model is proved finite convex, Euclidean 1-strongly convex, coercive and uniquely minimized at zero, with the literal coordinate formula in every dimension at least two. Every actual admissible full-BFGS run converges; actual second-Fréchet-derivative Hessian peaks diverge; RS fails on every neighborhood of zero with the required positive-band quantifier order. Rational value/first/second-derivative programs are computable and proved correct at every rational input, using exact finite prefixes and complete infinite-tail formulas. This verifies the Lean programs and printed mathematical oracle, not correspondence with a separate Python experimental program.

`audit/verify_normal_spike_examples.sh` reproduces the fresh main build, 98 transitive axiom reports, five exact types and nine source hashes. Independent reviews are `NORMAL_SPIKE_EXAMPLE_PEER_REVIEW.md` and `NORMAL_SPIKE_RATIONAL_PEER_REVIEW.md`; scratch backups match main up to import prefixes. These records supersede the earlier “remaining” entries for U.18–U.21 and the mathematical/executable rational oracle. The variable-jump U.7.2 model and its non-additive assertion remain under development; the latter requires the recorded `c≠0` correction. Global release status is maintained separately by the parent integration.

## Post-ninth variable-jump completion

The actual U.7.2 variable-jump family is now verified in twelve main `NormalSpikeVariable*.lean` modules: 83 declarations, five exact targets, a fresh pinned main build, standard transitive axioms only, and an independent review with no unresolved defect. The exact coordinate objective uses the original integral-defined scalar. Strong convexity, the actual quadratic branch Hessian matrices and displayed blocks, all actual supporting-vector tangential projections, Lipschitz tangent field, exact exceptional hyperplane, local full-BFGS basin and RS failure on every neighborhood are derived. The signed tangent height in the RS proof removes any final sign assumption on the original coupling vector.

The precise nonsplitting export excludes a differentiable smooth term plus any scalar function of the original fixed normal coordinate on every open neighborhood of zero. The source's `c≠0` correction is explicit in this target; zero coupling remains allowed for convergence and RS separation. `NORMAL_SPIKE_VARIABLE_STATEMENT_REVIEW.md` documents the correction without modifying the research source. All five targets and their strict type checks are in `NORMAL_SPIKE_VARIABLE_CONTRACTS.lean`; `verify_normal_spike_variable.sh` reproduces the main 83-declaration scope. Independent evidence is `NORMAL_SPIKE_VARIABLE_PEER_REVIEW.md`.

This completes the mathematical fixed-normal U claims tracked in this inventory, including the literal scalar and multidimensional examples. The separate experimental Python code is not claimed to be source-equivalent to the verified Lean rational oracle. Historical narrower records above remain intact and are superseded by their later explicit scopes; global release status is updated only by parent integration.
