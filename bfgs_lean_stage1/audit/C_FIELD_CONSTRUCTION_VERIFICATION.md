# C actual field construction and whole-level visibility

The main import `BfgsVerification.PlanarFieldVisibility` compiles with pinned Lean 4.19.0 and imports the new `PlanarActualCorners` and `PlanarFieldConstruction` modules. All 13 explicit theorems and the `CornerChart` structure passed type/declaration and transitive-axiom checks. The only axioms are standard `propext`, `Classical.choice`, and `Quot.sound`; the three recorded source hashes match. Evidence: `C_FieldConstructionAxiomChecks.lean`, `c_field_construction_build.log`, `c_field_construction_axioms.log`, `c_field_construction_declarations.json`, `c_field_construction_validation.log`.

```bash
source scripts/env.sh
lake build BfgsVerification.PlanarFieldVisibility
lake env lean audit/C_FieldConstructionAxiomChecks.lean
```

## Source hypotheses and constructed data

`exists_visible_comparison_field_on_compact_level` assumes only the actual finite convex objective, a compact subset of one objective level, literal strict contour geometry, the source smooth-or-regular-two-branch condition at every point of that set, and absence of affine-critical points there. It derives a vector field W, one positive constant η, and an open neighborhood N containing the entire compact set. W is locally Lipschitz at every point of N, and every actual supporting vector at every point of N pairs with W by at least η. On the base compact set, all actual supports at each point have exactly the same pairing with W.

The finite corner list, inverse-function curves, actual C1 level velocities, smooth cutoff functions, separated angular sectors and support-selection compatibility are all constructed. None is an extra final premise. `CornerChart` is only a transparent data package for the actual branches and inverse-function curve; `nonempty_cornerChart` constructs it from `TwoBranchRegularAt`, and `exists_finite_cornerCharts` constructs the finite family from the compact-level hypotheses. Independent active gradients are proved incompatible with actual differentiability. This closes the potentially missing case in the smooth-or-enumerated-corner cover. An empty corner family is supported.

The global field definition selects an actual support, but smooth uniqueness and whole-corner plateaus remove this arbitrary choice in all charts used. Strict contour geometry gives pairwise disjoint normal sectors. The cutoff construction uses actual C1 level velocities and yields positive normal pairing on their supports. Smooth points have the actual gradient formula, while corner points have the exact curve-velocity formula. Every actual support at a corner pairs to one; at a smooth point the supporting vector is unique. The resulting common-pairing identity is explicitly retained, since positivity alone is insufficient for the later transversality argument.

The neighborhood positivity proof uses the compact actual supporting graph and local Lipschitz regularity of W. A compact bad set and its closed projection yield a neighborhood bound at each base point. A finite subcover gives one η and one neighborhood for the whole compact set, without selecting a presumed limit point. Empty compact sets are handled explicitly. Local Lipschitz neighborhoods are extended to an open neighborhood and intersected with the visibility neighborhood.

## Remaining C work

This is a derived actual-objective field theorem, not the final affine-critical cluster theorem. Uniform endpoint transversality, the determinant logarithmic transport estimate, and the actual same-branch/crossing secant quotient remain to be assembled with the existing scalar full-BFGS energy contradiction. The original branch convexity needed for the secant argument is retained as a separate source obligation; it is unnecessary for the field geometry proved here. The original research sources are unchanged.
