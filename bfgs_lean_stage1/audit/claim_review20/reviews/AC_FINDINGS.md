# Skeptical source-to-proof review: A's gap and C's principal theorem

## Result and limits

**No source/statement defect was found in the selected principal claims.** The
review concerns original `affine_geometry.tex` lines 60–77 and `C.tex` lines
30–63, with C's semialgebraic application at lines 335–340. It is not an
independent verification of every claim in all fourteen report chapters. In
particular it does not turn A's expressly labelled general-dimensional
conjecture into a theorem, or certify any historical verification assertion.

This conclusion is based on reading the definitions and proof bodies below,
and compiling independently expanded source contracts. It does not merely
repeat a completion register or typecheck a theorem of an opaque named target.
No main source was edited. All new Lean is a standalone review driver importing
existing main modules. It introduces no algorithm, assumed oracle, mathematical
axiom, `sorry`, `admit`, or external-computation proof mechanism.

`GeometryContracts.lean` freshly compiled with ten named review declarations,
26 selected existing declaration type/ordinary-axiom reports, and six strict
comparisons between central declarations/target definitions and independently
written signatures. All proof dependencies reported by ordinary `#print
axioms` are contained in `propext`, `Classical.choice`, `Quot.sound`. Definitions
are audited too; they are not counted as new main-library theorems.

## What was unfolded

* `F : Vec n → ℝ` is everywhere real-valued. Convexity is `ConvexOn ℝ univ F`.
  It does not assume differentiability at arbitrary objective points.
* `subdifferential F p` is literally the set of all `g` satisfying
  `∀ z, dot g (z-p) ≤ F z-F p`. The affine hull uses signed coefficients;
  it is not the convex hull or the active set of a user-provided finite model.
  The coordinate and Euclidean affine-hull predicates are related by an actual
  invertible linear-coordinate proof. The review's `rawCritical_iff` checks
  that connection against this literal support set.
* `IsSemialgebraicObjective` means the actual graph of F has a finite Boolean
  formula of real polynomial equalities/strict inequalities. It does not
  include projection closure, paths, finite components, or finite values as
  definitional conditions. `raw_A_finite_values_and_gap` replaces the predicate
  with the explicit existential polynomial formula in its hypothesis.
* `AdmissibleBFGSRun` contains only finite convexity, the actual sequences,
  fixed `0<c₁<c₂<1`, `H₀.PosDef`, positive lengths, nonzero accepted gradients,
  actual Fréchet derivatives, accepted displacement, full inverse update,
  and Armijo/weak Wolfe. No all-iterate SPD, bounded gradients, summability,
  iterate limit, matrix limit, finite path length, or field is a record field.
  `raw_C_cluster_and_convergence` removes the record premise completely and
  constructs it from these displayed data. Its update uses literal entries
  `sᵢyⱼ`, `yᵢsⱼ`, `sᵢsⱼ` and actual matrix multiplication. Its derivative is
  the explicit sum of coordinate projection functionals.
* `clusterSet x` is actual `MapClusterPt p atTop x`. It is neither an input
  compact set nor a selected singleton. `argmin F` means all global minimizers.
  The convergence contract includes actual Euclidean `infDist`, through the
  explicit finite-dimensional L² coordinate realization; it does not silently
  identify the internal finite-Pi norm with Euclidean length.
* A piecewise smooth path contains a real curve, continuity on `[0,1]`, both
  actual endpoints, image containment, a finite exceptional set, and actual
  smoothness at every other interior time. `raw_semialgebraic_finite_path_cover`
  unfolds all of these fields and derives the finite family from the genuine
  polynomial-formula hypothesis alone.

## A: none of the required geometric conclusions is an assumed premise

The critical chain was read through the following bodies:

1. `AffineBoundedRepresentation` obtains at most `n+1` members of the original
   support set from an affine-independent spanning subset and finite-dimensional
   linear algebra. The coefficients are unrestricted real numbers with sum one.
   `AffineCriticalWitness` proves the exact finite union of projected signed
   witness sets. The `m=0` case cannot provide coefficients summing to one; the
   proof excludes it, rather than allowing an empty false witness.
2. `AffineCriticalDefinability` derives the actual supporting graph and actual
   affine-critical graph. Its calls to projection closure use the proved
   `coordinate_projection_semialgebraic`, not a typeclass oracle or a remaining
   `hprojection` input. `GeneralCoordinateProjection` performs finite-coordinate
   induction, reducing a coordinate to `BooleanPolynomialProjection`; the latter
   uses simultaneous sign patterns with one common scalar witness for every
   polynomial atom. It does not distribute an existential separately over atoms.
3. `SemialgebraicSmoothCover` performs natural-number dimension induction. The
   `SmoothCoverDimension` assumption appearing in helper lemmas is the previous
   dimension and is discharged by that induction in the final theorem. Its
   proof handles every zero-fiber pattern and every attained root signature.
   Signatures fix actual specialized degree, distinct real-root count, and total
   real-root multiplicity. The final finite cover is not supplied by the caller.
   `FiniteCoverOnSignature` derives ordered-root graph/band cells and refines by
   the actual finite boundary-sign table; the lower-dimensional induction is
   applied to these actual semialgebraic strata. `FiniteSmoothCovers` selects
   whole sign-compatible pieces and proves the union is exactly the input set.
4. `semialgebraic_affine_critical_values` applies this constructed cover to the
   **lifted actual critical graph**, then `finite_critical_values_of_smooth_graph_cover`.
   The latter is indeed a conditional helper, but its finite-cover premise has
   just been derived. Each supplied curve stays on `z_none=F(z_some)`; the graph
   projection proof obtains differentiability of both its point coordinates and
   F composed with those coordinates from the same smooth graph curve. It does
   not assume F is differentiable on the critical set.
5. `AffineSupportPath.supporting_path_derivative_eq` uses the literal global
   supporting inequality to make `F(p(u))-g·(p(u)-p(t))` have a local minimum.
   Its actual two-sided derivative therefore gives `g·p'(t)=(F∘p)'(t)` for
   every support. Affine pairing with zero forces this derivative to zero.
   `AffinePathConstancy` splits at a finite set of exceptional times and uses
   continuity at those times and at endpoints to obtain true endpoint equality.
6. `FiniteAffineCriticalValues` derives a positive gap above the attained
   minimum from the finite **actual** image of the affine-critical set.
   `semialgebraic_low_affine_critical_gap` supplies that finite image theorem
   directly. The expanded review adapter concludes the literal global minimum
   inequality `∀ z, F p≤F z`, equivalently membership of zero in the support set.

Thus the older helpers whose statements explicitly assume a path cover or a
finite value set are not substitutes for the original A theorem: the final
application proves their hypotheses. The finite-value theorem itself does not
need attainment; attainment is used only for the source's low-gap conclusion.
The constructions include dimension zero and empty critical strata.

## Path semantics and the literal A composition statement

Two different notions remain explicitly named. `connectedComponentIn` denotes
ordinary topological connected components. `continuousSemialgebraicComponent`
is the class of endpoints reachable by an arbitrary continuous curve with a
semialgebraic restricted graph. Its definition has **no smoothness requirement**.
`ContinuousSemialgebraicComponents` upgrades that very same curve using the
proved finite-exception coordinatewise smoothness theorem and proves equality
with the enriched smooth-path classes. It derives finite, semialgebraic,
internally path-connected actual classes. The actual critical-set application
also proves F constant on each such class. Separately, ordinary components are
finite and semialgebraic and F is constant on them. This review does not identify
the two component operators by definition or claim an unexamined theorem that
they are equal. The low-gap proof only needs the constructed finite graph cover.

`ObjectiveSemialgebraicComposition` additionally proves the literal statement
for an arbitrary actual continuous semialgebraic input curve, by projecting the
two actual graphs with a common point witness and deriving scalar regularity.
`raw_A_path_and_composition` checks that both the identical input curve and
F∘that curve are smooth away from one derived finite exceptional set. The
meaning is continuity on the closed parameter interval and smoothness on its
open pieces. No ambient smoothness at endpoints or exceptional breakpoints is
claimed. This is sufficient for the source's piecewise-C¹ constancy argument.

## C: the dynamical conclusions are proved, not supplied

1. `PositiveUpdate.fullBFGS_positive_invariants` inducts from `H₀.PosDef`.
   Current SPD and nonzero gradient make q positive; weak Wolfe and positive
   length give positive curvature; the actual inverse update then preserves
   SPD. `ObjectiveRun.toFullBFGSRun` fills its all-iterate matrix invariants from
   these theorems. Its scalar q/d/beta are definitionally the same data.
2. `ClusterSetGeometry.positive_limit_of_no_affineCritical_cluster` constructs
   the monotone objective limit. Compactness supplies an actual cluster point;
   if the limit were minimal, it would be stationary and affine critical. Hence
   the contradiction hypothesis forces a strictly positive limiting level.
3. `StrictContours` proves d→0 from the actual Armijo budget. A subsequence of
   actual consecutive pairs with nonvanishing separation gives a constant-level
   segment by convex support inequalities. The lower objective value ensures
   this entire segment is in the actual sublevel frontier. The source contour
   hypothesis forces its endpoints equal. Thus step convergence is derived.
4. The finite corner list in `PlanarActualCorners` is derived from the actual
   compact level and regular local two-branch structure, including the empty
   list when all points are smooth. The chart curve is supplied by the actual
   inverse function theorem, and its common gradient rate by differentiation.
   `PlanarFieldConstruction` builds disjoint smooth cutoffs and one actual
   field. Its globally arbitrary support selection is not assumed continuous:
   actual gradient uniqueness removes it at smooth points and the entire corner
   neighborhood lies on one fixed cutoff plateau, where the field is the C¹
   level velocity composed with F. Local Lipschitz regularity and visibility
   against **every** support are derived there.
5. `exists_secant_structured_visible_field` constructs **one and the same field**
   with the visibility, regularity, common pairing and local secant estimates.
   `PlanarRunTransport` traps complete sufficiently late segments near the
   **whole** cluster set. Its determinant lower bound comes from a compact
   subsequence contradiction with actual gradient/support limits and actual
   weak Wolfe. It does not assume a limiting gradient or eigenspace.
6. `PlanarCrossingSecant` uses an actual tie on a crossing segment from the
   intermediate value theorem, cancels the actual branch jump against the
   constructed field, and bounds the remaining terms. It does not assume
   finitely many switches along a segment. `PlanarCompactSecant` turns the local
   estimates into one uniform bound by a finite buffered cover.
7. `PlanarSecantRun` obtains transport and secant bounds for that same field,
   aligns their tail indices, and invokes `scalar_log_transport_tail_incompatible`.
   This last theorem derives gradient bounds and summability from the compact
   actual sublevel before applying the already proved full-BFGS reciprocal-mean
   divergence. There is no extra frame existence or scalar-hierarchy premise in
   `planar_affineCritical_cluster`.
8. `PlanarConvergence` invokes the actual cluster theorem, uses source affine
   correctness to make the cluster point a global minimizer, and derives value
   and Euclidean solution-distance convergence. Uniqueness is used only for
   convergence to one point. In the semialgebraic basin, A's finite actual values
   supply affine correctness; ε is selected **before** quantifying over all
   runs, all SPD initial matrices and all allowed fixed line-search constants.

## Scope boundaries that must not be erased

* C's compact sublevel, strict positive contours, and stated regular switching
  conditions are source assumptions. A alone does not prove that arbitrary
  finite convex semialgebraic objectives generate an affine-critical cluster.
* `ConvexTwoBranchRegularAt` retains actual local convex C² branches, both active
  at the point, and nonzero planar determinant of their actual gradients. It
  does not merely assume a crossing certificate. Convex neighborhoods can be
  obtained by shrinking source neighborhoods; determinant nonzero is exactly
  planar linear independence. No structure is imposed at affine-critical points.
* The central C target permits b equal to the minimum in addition to the source's
  b greater than the minimum. This is a stronger harmless extension; the source
  positive-b range is present. An infinite nonstationary run at the minimum
  cannot occur, as expected. It does not narrow the original theorem's range.
* Infinite nonstationary accepted runs are the source's domain. The theorem
  does not assert existence of a differentiable acceptable step on every ray;
  source C explicitly excludes that assertion. Nor is iterate convergence
  claimed without the source's uniqueness or affine-correctness conditions.
* This bounded review does not separately prove existence of an infinite run
  for every objective satisfying the geometric assumptions. It verifies the
  source's universal conditional theorem and inspects its record for hidden
  contradictory assumptions. No such added assumption was found.

## Reproduction and evidence

The Lean source is copied byte for byte from the reviewed standalone audit: [source](../sources/GeometryContracts.lean). The completed review-authoring ordinary compiler output is retained as [reviewed log](../reviewed_logs/AC.log); it is evidence from this claim review’s authoring run, and public reproduction does not read a scratch directory. The source findings above concern original report claims, not a replay of historical numerical executions.

From `bfgs_lean_stage1`, run `python3 scripts/verify_report_claim_review_20.py --run` for an incremental pinned main-library build followed by fresh compilation of all delivered audit sources. This uses existing build artifacts; it is not described as a clean rebuild. Run the same command without `--run` to validate completed public logs and hashes. If the default fresh directory already exists, `--run` automatically selects a unique UTC directory and prints the exact validation command; existing evidence is preserved. An explicit `--run-dir audit/claim_review20/runs/<new-name>` is also supported.

[Jobs and exact report inventories](../jobs.json) distinguish ordinary report occurrences from distinct declarations. [Fresh summary](../fresh/SUMMARY.json) exists only after an actual successful public execution. No main proof, central import, central audit, or closed status is changed by this bounded reproduction.
