# Full RS→IR proof design

Status: read-only design, after inspecting the pinned mathlib sources and the compiled project lemmas. No new Lean source or compiler claims are made in this design. Source target is `report/chapters/R.tex`, lines 99–129, the missing direction of R:thm:equiv. The original research source is unchanged.

Implementation follow-up: this design has now been carried through in `ConvexDifferentiability.lean`, `RadialApproximation.lean`, and `RadialReverse.lean`. All 18 new declarations compile and pass the transitive axiom audit. See `audit/RADIAL_REVERSE_STATEMENT_REVIEW.md` for the final exact scope and evidence; the design below is retained as the pre-implementation record.

## Exact intended endpoint

```lean
theorem inward_of_radial_on_compact_sublevel
    {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (b : ℝ) (hb : F star < b)
    (hK : IsCompact {x : Vec n | F x ≤ b})
    (hRS : RadialCertificate.HasRadialSecantBounds F {x | F x ≤ b} star) :
    RadialCertificate.HasInwardTaylorBounds F {x | F x ≤ b} star
```

Combine this with the existing `radial_of_inward_on_compact` to export the exact RS↔IR equivalence on the same compact sublevel. Neither uniqueness nor any regularity of the gradient on a neighborhood is needed. The sampled inner point must not be assumed differentiable in the final theorem. The strict inequality `F star < b` supplies nonempty interior for approximation at the top boundary; it is a genuine source hypothesis, not an additional condition.

## Key simplifications

1. **Avoid transporting null sets under affine maps.** For fixed `t < 1`, let `A(w)=inwardPoint star w t`, equivalently `AffineMap.homothety star (1-t)`. Both F and `F ∘ A` are finite convex functions, so both are almost everywhere differentiable by the same Rademacher lemma. At a point where `F ∘ A` is differentiable, compose it with the explicit affine inverse `AffineMap.homothety star (1-t)⁻¹` to obtain differentiability of F at A(w). Thus the good set `{w | DifferentiableAt F w ∧ DifferentiableAt F (A w)}` is dense. No Jacobian, determinant scaling, quasi-measure-preserving, or null-set preimage theorem is required.
2. **Avoid a separate uniform Lipschitz-on-K theorem for the band margin.** At the original differentiable x, the existing supporting inequality gives `F(A x) ≥ F x − t*dot g (x−star)`. The already-verified actual Euclidean gradient/radius bounds give `|dot g (x−star)| ≤ G*R`. Hence `F(A x) ≥ F star + 3η/4` for the source `t ≤ η/(4GR)`, without a derivative at A(x).
3. **Use openness for every approximating pair's band membership.** The original inner point has the strict margin `F(A x) > F star + η/2`. The set `O={w | F star+η/2 < F(A w)}` is open and contains x. Choose the jointly differentiable sequence in `interior K ∩ O`. Convexity and the global minimum imply `F(A w) ≤ F w` for `0≤t≤1`; this supplies pair ordering and outer-band membership automatically. There is no need to preserve the original η-band exactly along the approximation.

## Verified API inventory from the pinned mathlib source

The project imports `Mathlib` through Definitions, but explicit imports may improve dependency readability.

| API | Location and use |
|---|---|
| `ConvexOn.exists_lipschitzOnWith_of_isBounded` | `Analysis/Convex/Continuous.lean:71`: convexity on `ball x₀ r`, `r′<r`, and bounded image of the larger ball produce `∃ C : ℝ≥0, LipschitzOnWith C F (ball x₀ r′)`. |
| `ConvexOn.locallyLipschitz`, `...locallyLipschitzOn` | Same file, lines 182, 215. Available, but the countable-ball construction below is more direct than unpacking a local cover. No corresponding global locally-Lipschitz Rademacher wrapper was found in the pinned tree. |
| `LipschitzOnWith.ae_differentiableWithinAt_of_mem` | `Analysis/Calculus/Rademacher.lean:366`: `∀ᵐ x ∂μ, x∈s → DifferentiableWithinAt ℝ F s x`. Domain/codomain finite dimensional; μ is additive Haar. |
| `DifferentiableWithinAt.differentiableAt` | Converts at a point in the open ball, using `isOpen_ball.mem_nhds`. |
| `MeasureTheory.ae_all_iff` | Combines the countable natural-number family of almost-everywhere implications. |
| `MeasureTheory.Measure.dense_of_ae` | `MeasureTheory/Measure/OpenPos.lean:105`: an a.e. property is dense for a measure positive on nonempty open sets. |
| `MeasureTheory.isAddHaarMeasure_volume_pi` | `MeasureTheory/Measure/Lebesgue/EqHaar.lean:120`: canonical volume on `Fin n → ℝ` has the required Haar instance. The theorem itself is `inferInstance`; no custom measure construction is needed. |
| `ConvexOn.comp_affineMap` | `Analysis/Convex/Function.lean:936`: precomposition by an actual affine map preserves convexity; preimage of univ simplifies to univ. |
| `AffineMap.homothety`, `homothety_apply`, `homothety_mul_apply`, `homothety_one` | `LinearAlgebra/AffineSpace/AffineMap.lean:756–783`. These give the inward map and its inverse. Differentiability of each map also follows directly by expanding to `a • (w−star)+star` and using the standard derivative combinators. |
| `ConvexOn.convex_le` | `Analysis/Convex/Function.lean:235`: convexity of K after simplifying membership in univ. |
| `Convex.closure_interior_eq_closure_of_nonempty_interior` | `Analysis/Convex/Topology.lean:290`: K is the closure of its interior because it is convex, closed, and has an interior point. |
| `IsOpen.closure_inter`, `Dense.open_subset_closure_inter` | `Topology/Neighborhoods.lean:303,306`: restrict the boundary approximation to O, then intersect the open set with the dense jointly differentiable set. |
| `mem_closure_iff_seq_limit` | `Topology/Sequences.lean:104`: obtain an actual ℕ-indexed sequence in the required set converging to x. |
| `DifferentiableAt.hasFDerivAt` | `Analysis/Calculus/FDeriv/Basic.lean:556`: actual derivative functional at each selected differentiable point. |
| `Pi.single_smul`, `Finset.univ_sum_single` | Coordinate expansion used to represent any derivative functional by `gradientFunctional`. The former is in `Algebra/GroupWithZero/Action/Pi.lean:61`. |

## Suggested intermediate statements and proof order

### 1. Coordinates for arbitrary actual derivatives

Prove that every continuous linear functional `ℓ : Vec n →L[ℝ] ℝ` is `gradientFunctional g` with `g i = ℓ (Pi.single i 1)`. Expand each vector as `∑ i, v i • Pi.single i 1`, distribute ℓ, and use the existing exact `gradientFunctional_apply`.

Export either a total coordinate-gradient definition built from `fderiv ℝ F x`, or a theorem:

```lean
DifferentiableAt ℝ F x → ∃ g : Vec n,
  HasFDerivAt F (gradientFunctional g) x
```

This is a representation theorem; it must be proved rather than assume gradients chosen at Rademacher points.

### 2. Almost-everywhere differentiability of finite convex F

For each natural k, restrict F to `ball 0 (k+1)` and obtain Lipschitz continuity on `ball 0 k`. The larger ball's image is bounded because it is contained in the continuous image of the compact closed ball. Apply Rademacher within the smaller ball and convert to differentiability at each point of that open ball. Intersect these a.e. statements using `ae_all_iff`. Given x, choose `k > ‖x‖` by `exists_nat_gt`; this covers the whole finite coordinate space.

Suggested export:

```lean
theorem convex_ae_differentiable {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) :
    ∀ᵐ x ∂(volume : Measure (Vec n)), DifferentiableAt ℝ F x
```

No positivity assumption on dimension is required. Rademacher's final theorem is stated without `Nontrivial E`.

### 3. Joint differentiability under fixed inward contraction

Intersect the previous a.e. theorem for F and for `F ∘ AffineMap.homothety star (1-t)`. For `t≠1`, the inverse dilation is differentiable and exactly inverts the original map, so chain-rule composition supplies the missing derivative at the inner endpoint. Apply `Measure.dense_of_ae`.

Suggested export:

```lean
theorem dense_inward_differentiable_pairs ... (ht : t ≠ 1) :
  Dense {w | DifferentiableAt ℝ F w ∧
    DifferentiableAt ℝ F (inwardPoint star w t)}
```

This avoids any assertion that two arbitrary dense sets have dense intersection: the intersection is first proved **almost everywhere**, then dense.

### 4. Boundary-safe approximation on the same K

Continuity gives `star∈interior K` from `F star<b`. Since K is closed convex, every x∈K is in `closure (interior K)`. For any open O containing x, the APIs above give

`x ∈ closure ((interior K ∩ O) ∩ jointlyDifferentiableSet)`.

The sequence theorem then supplies xj in this exact set and xj→x. Inner-point containment follows from convexity of the sublevel and `star∈K`; alternatively derive it from `F(A xj)≤F xj≤b`.

### 5. Uniform parameters, paired estimates, and the limiting inequality

Fix η>0. Derive positive G,R from `convex_gradient_bound_on_compact` and `compact_sqNorm_radius`. Obtain the RS constant at η/2, replace it by `C′=max(C,0)`, and choose

`θ=min(1/2, η/(4GR))`, `M=8C′`.

For any source endpoint x,g and any `0<t≤θ`:

- The original supporting plane proves `F(A x)≥Fstar+3η/4`, as above.
- Choose `O={w | Fstar+η/2<F(A w)}` and the jointly differentiable sequence.
- Choose actual gradients gj,hj at xj,A(xj) via the representation theorem.
- The source RS hypothesis at η/2 applies to each positive-curvature pair; zero curvature is already covered by `inward_error_le_of_pair_radial`.
- That existing lemma gives `supportingError F xj gj (A xj) ≤ 4C′ t²` for every j.
- Existing `convex_gradients_tendsto_at_differentiable` gives gj→g. No convergence of hj is needed.
- Continuity of F, the inward affine map, and the actual dot product, together with `inward_error_eq`, gives convergence of the errors to `supportingError F x g (A x)`.
- Pass the uniform inequality to the limit. The upper bound is `(M/2)t²`, since M=8C′. The lower bound is the existing convex supporting-error nonnegativity theorem. Handle t=0 directly.

All constants are chosen before x,g,t. The approximate endpoints stay on the original compact sublevel and the RS η/2-band. No enlarged-domain RS hypothesis is introduced.

## Gap assessment and implementation boundary

No mathematical gap was found in the source reverse implication under its full setup (`F` finite convex, attained minimum, compact sublevel, `b>F*`). The earlier paired lemma is insufficient by itself, and the proof must add both joint differentiability and top-boundary approximation as above. Dropping `b>F*` or replacing the compact sublevel by an arbitrary compact K would require a different statement: the interior approximation used here need not hold.

The source states finite C, not C≥0. Replacing it by `max(C,0)` before setting M is an explicit harmless normalization; this preserves the hypothesis and ensures the scalar paired lemma applies. The final statement can keep the source existential constants unchanged in strength.

A bounded implementation tranche can use new files `ConvexDifferentiability.lean` (coordinate gradient, a.e./joint density), `RadialApproximation.lean` (boundary-safe sequence and value margin), and `RadialReverse.lean` (full reverse and equivalence). Each should be compiled and axiom-audited after implementation; no status should label this design or the pre-existing paired reverse lemma as the full theorem.
