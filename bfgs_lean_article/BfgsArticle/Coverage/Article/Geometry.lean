import MixedBenchmark
import ArticleGeometry
import ConvexBalance
import BfgsVerification.DEmbeddingCenter
import BfgsVerification.PointwiseCertificateFeasibility

/-!
# Lean coverage of `paper/sections/geometry.tex`

Coverage theorems for the claims made only in Section `art:geometry` ("What the
results say about nonsmooth BFGS"), its Figure `art:gradient-geometry` and its
Table `art:positive-outcomes`. Register:
`editorial/lean_coverage/register/A_geometry.json`.

Conventions. The mixed ridge `F(u,v)=u^2+|v|` is
`BfgsVerification.UnexcitedMetric.objective`, literally `(x 0)^2+|x 1|` on
`Vec 2`; its actual gradient is `coordinateGradient` (coordinates of the Fréchet
derivative). The seed slopes `g_0=(1,0)`, `g_1=(-1,-1/8)`, `g_2=(c_∘,d_∘)` are
`SeedOrbit.gradient seedC seedD`, where `(seedC, seedD)` is the isolated root of
Appendix `art:seed_certificate`, and the seed objective `G(z)=max_i g_i^T z` is
`SeedOrbit.objective seedC seedD`. The affine/convex balance facts are stated in
`EuclideanSpace ℝ (Fin n)` with its inner product.
-/

noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Set Filter

namespace BfgsCoverage.Article.Geometry
open BfgsVerification

/-! ## The mixed ridge -/

/-- Item `A/geometry/prose/001` (`paper/sections/geometry.tex:4-5`):
"Reaching $v=0$ does not eliminate the horizontal error $u^2$."
On the nonsmooth line `v=0` the mixed ridge equals `u^2`, which exceeds the
minimum value `F(0,0)=0` whenever `u ≠ 0`. -/
theorem horizontal_error_on_line (u : ℝ) :
    UnexcitedMetric.objective ![u, 0] = u ^ 2 ∧
      (u ≠ 0 → UnexcitedMetric.objective 0 < UnexcitedMetric.objective ![u, 0]) := by
  have h : UnexcitedMetric.objective ![u, 0] = u ^ 2 := by
    simp [UnexcitedMetric.objective]
  refine ⟨h, fun hu => ?_⟩
  rw [h]
  simpa [UnexcitedMetric.objective] using sq_pos_of_ne_zero hu

/-- Item `A/geometry/prose/002` (`paper/sections/geometry.tex:5-6`):
"Yet the vertical gradient jump does not remove the direction that can reduce
this error." For `u ≠ 0` the horizontal direction `(-u,0)` strictly lowers
`F(u,v)=u^2+|v|` from every point `(u,v)`, on either side of the jump line `v=0`
and on it: `F((u,v)+t(-u,0)) < F(u,v)` for `0<t≤1`. -/
theorem horizontal_direction_reduces_error {u : ℝ} (hu : u ≠ 0) (v : ℝ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    UnexcitedMetric.objective (![u, v] + t • ![-u, 0]) < UnexcitedMetric.objective ![u, v] := by
  have hu2 := sq_pos_of_ne_zero hu
  simp only [UnexcitedMetric.objective, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero]
  have he : (u + t * -u) ^ 2 = (1 - t) ^ 2 * u ^ 2 := by ring
  rw [he]
  have hlt : (1 - t) ^ 2 < 1 := by nlinarith
  nlinarith

/-- The actual gradient of the mixed ridge off the line `v=0`. -/
theorem gradient_off_line {p : Vec 2} (hp : p 1 ≠ 0) :
    coordinateGradient UnexcitedMetric.objective p = ![2 * p 0, Real.sign (p 1)] := by
  have he : p = ![p 0, p 1] := by
    ext i
    fin_cases i <;> rfl
  have hg := ArticleGeometry.mixed_ridge_gradient (u := p 0) hp
  rw [← he] at hg
  exact PointwiseFeasibility.coordinateGradient_eq hg

/-- The mixed ridge is not differentiable on the line `v=0`. -/
theorem not_differentiable_on_line {p : Vec 2} (hp : p 1 = 0) :
    ¬ DifferentiableAt ℝ UnexcitedMetric.objective p := by
  intro hd
  have hl : DifferentiableAt ℝ (fun t : ℝ => p + t • (![0, 1] : Vec 2)) 0 :=
    (differentiableAt_const p).add (differentiableAt_id.smul_const _)
  have hd' : DifferentiableAt ℝ UnexcitedMetric.objective (p + (0 : ℝ) • (![0, 1] : Vec 2)) := by
    simpa using hd
  have hc := (hd'.comp (0 : ℝ) hl).sub_const ((p 0) ^ 2)
  have hf : (fun t : ℝ => (UnexcitedMetric.objective ∘ fun t : ℝ => p + t • (![0, 1] : Vec 2)) t
      - (p 0) ^ 2) = fun t : ℝ => |t| := by
    funext t
    simp only [Function.comp_def, UnexcitedMetric.objective, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
      add_zero, mul_one, hp, zero_add]
    ring
  rw [hf] at hc
  exact not_differentiableAt_abs_zero hc

/-- Item `A/geometry/prose/003` (`paper/sections/geometry.tex:6-7`):
"Along $v=0$ the limiting gradients are $(2u,1)$ and $(2u,-1)$. Their difference
is vertical." A vector `g` is a limit of actual gradients `∇F(p_k)` at
differentiable points `p_k → (u,0)` exactly when `g=(2u,1)` or `g=(2u,-1)`; the
difference of these two vectors is `(0,2)`. -/
theorem limiting_gradients (u : ℝ) :
    (∀ g : Vec 2,
      (∃ p : ℕ → Vec 2, Tendsto p atTop (𝓝 ![u, 0]) ∧
          (∀ k, DifferentiableAt ℝ UnexcitedMetric.objective (p k)) ∧
          Tendsto (fun k => coordinateGradient UnexcitedMetric.objective (p k)) atTop (𝓝 g)) ↔
        (g = ![2 * u, 1] ∨ g = ![2 * u, -1])) ∧
      (![2 * u, 1] : Vec 2) - ![2 * u, -1] = ![0, 2] := by
  refine ⟨fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨p, hp, hd, hg⟩
    have hp1 : ∀ k, p k 1 ≠ 0 := fun k h => not_differentiable_on_line h (hd k)
    have hgk : ∀ k, coordinateGradient UnexcitedMetric.objective (p k) = ![2 * p k 0, Real.sign (p k 1)] :=
      fun k => gradient_off_line (hp1 k)
    simp only [hgk] at hg
    have hg0 := (continuous_apply 0).continuousAt.tendsto.comp hg
    have hg1 := (continuous_apply 1).continuousAt.tendsto.comp hg
    have hp0 := (continuous_apply 0).continuousAt.tendsto.comp hp
    simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg0 hg1 hp0
    have h0 : g 0 = 2 * u := tendsto_nhds_unique hg0 (hp0.const_mul 2)
    have hmem : ∀ k, Real.sign (p k 1) ∈ ({1, -1} : Set ℝ) := by
      intro k
      rcases lt_or_gt_of_ne (hp1 k) with h | h
      · simp [Real.sign_of_neg h]
      · simp [Real.sign_of_pos h]
    have hclosed : IsClosed ({1, -1} : Set ℝ) := (Set.toFinite _).isClosed
    have h1 : g 1 ∈ ({1, -1} : Set ℝ) := hclosed.mem_of_tendsto hg1 (Eventually.of_forall hmem)
    rcases h1 with h1 | h1
    · left
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · right
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
  · intro hg
    have hs : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    rcases hg with rfl | rfl
    · refine ⟨fun k => ![u, 1 / ((k : ℝ) + 1)], ?_, ?_, ?_⟩
      · rw [tendsto_pi_nhds]
        intro i
        fin_cases i
        · simp
        · simpa using hs
      · intro k
        exact (ArticleGeometry.mixed_ridge_gradient (u := u) (hpos k).ne').differentiableAt
      · have he : ∀ k : ℕ, coordinateGradient UnexcitedMetric.objective ![u, 1 / ((k : ℝ) + 1)]
            = ![2 * u, 1] := by
          intro k
          rw [gradient_off_line (by simpa using (hpos k).ne')]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [Real.sign_of_pos (hpos k)]
        simp only [he]
        exact tendsto_const_nhds
    · refine ⟨fun k => ![u, -(1 / ((k : ℝ) + 1))], ?_, ?_, ?_⟩
      · rw [tendsto_pi_nhds]
        intro i
        fin_cases i
        · simp
        · simpa using hs.neg
      · intro k
        exact (ArticleGeometry.mixed_ridge_gradient (u := u) (neg_ne_zero.mpr (hpos k).ne')).differentiableAt
      · have he : ∀ k : ℕ, coordinateGradient UnexcitedMetric.objective ![u, -(1 / ((k : ℝ) + 1))]
            = ![2 * u, -1] := by
          intro k
          rw [gradient_off_line (by simpa using (hpos k).ne')]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [Real.sign_of_neg (neg_neg_of_pos (hpos k))]
        simp only [he]
        exact tendsto_const_nhds
  · ext i
    fin_cases i <;> norm_num

/-- Item `A/geometry/prose/004` (`paper/sections/geometry.tex:7-9`):
"At a point with $u\ne0$, the horizontal vector $(-u,0)$ has the same strictly
negative pairing $-2u^2$ with both gradients." The gradients are the limiting
gradients `(2u,1)` and `(2u,-1)` of `limiting_gradients`. -/
theorem equal_negative_pairing {u : ℝ} (hu : u ≠ 0) :
    dot (![2 * u, 1] : Vec 2) ![-u, 0] = -2 * u ^ 2 ∧
      dot (![2 * u, -1] : Vec 2) ![-u, 0] = -2 * u ^ 2 ∧ -2 * u ^ 2 < 0 :=
  ArticleGeometry.mixed_ridge_equal_descent u hu

/-- Item `A/geometry/disp/001` (`paper/sections/geometry.tex:10-13`), equation `art:mixed-inward-remainder`:
$$F((1-\tau)(u,v))-F(u,v)+\tau\nabla F(u,v)^T(u,v)=\tau^2u^2\qquad(v\ne0,\ 0\le\tau\le1),$$
with `F(u,v)=u^2+|v|` and its actual gradient `∇F(u,v)` (which exists for `v ≠ 0`). -/
theorem mixed_inward_remainder {u v τ : ℝ} (hv : v ≠ 0) (_hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    UnexcitedMetric.objective ((1 - τ) • ![u, v]) - UnexcitedMetric.objective ![u, v] +
        τ * dot (coordinateGradient UnexcitedMetric.objective ![u, v]) ![u, v] = τ ^ 2 * u ^ 2 := by
  have hg := ArticleGeometry.mixed_ridge_gradient (u := u) hv
  rw [PointwiseFeasibility.coordinateGradient_eq hg]
  simpa using ArticleGeometry.mixed_ridge_inward hg hτ1

/-- Item `A/geometry/prose/005` (`paper/sections/geometry.tex:14-15`):
"Thus the nonsmooth part is exactly linear under inward scaling, while the
smooth part contributes a quadratic remainder." For `τ ≤ 1` the nonsmooth part
satisfies `|(1-τ)v| = (1-τ)|v|`, so its inward first-order remainder vanishes at
every `v ≠ 0` (where its derivative is `sign v`); the smooth part `u^2` has
inward remainder `((1-τ)u)^2-u^2+τ(2u)u = τ^2u^2`. -/
theorem inward_split (u v τ : ℝ) (hτ : τ ≤ 1) :
    |(1 - τ) * v| = (1 - τ) * |v| ∧
      (v ≠ 0 → |(1 - τ) * v| - |v| + τ * (Real.sign v * v) = 0) ∧
      ((1 - τ) * u) ^ 2 - u ^ 2 + τ * (2 * u * u) = τ ^ 2 * u ^ 2 := by
  have hlin : |(1 - τ) * v| = (1 - τ) * |v| := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hτ)]
  refine ⟨hlin, fun hv => ?_, by ring⟩
  rw [hlin]
  rcases lt_or_gt_of_ne hv with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

/-! ## The seed corner -/

/-- Item `A/geometry/prose/014` (`paper/sections/geometry.tex:35-36`), with the slopes of
lines 33-35: the slopes are "$g_0=(1,0)$, $g_1=(-1,-1/8)$ and $g_2=(c_\circ,d_\circ)$ ... They are affinely
independent, so no nonzero direction pairs equally with all three." -/
theorem seed_affinely_independent :
    SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD =
        ![![1, 0], ![-1, -1 / 8], ![SeedOrbit.seedC, SeedOrbit.seedD]] ∧
      AffineIndependent ℝ (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD) ∧
      ∀ (v : Vec 2) (κ : ℝ),
        (∀ j, dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) v = κ) → v = 0 := by
  refine ⟨?_, ArticleGeometry.seed_affine_independent,
    fun v κ h => ArticleGeometry.seed_equal_pairings_force_zero h⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Item `A/geometry/prose/015` (`paper/sections/geometry.tex:36-38`):
"Yet $(-1,16)$ has negative pairing with each, and zero is outside their convex
hull." -/
theorem seed_common_descent :
    (∀ j, dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) ![-1, 16] < 0) ∧
      (0 : Vec 2) ∉ convexHull ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) :=
  ⟨ArticleGeometry.seed_strict_common_descent, ArticleGeometry.seed_convex_hull_excludes_zero⟩

/-- Item `A/geometry/prose/016` (`paper/sections/geometry.tex:38`):
"The corner is therefore nonstationary." Zero is not a subgradient of the seed
objective `G(z)=max_i g_i^T z` at the corner `z=0`; indeed `G` decreases at unit
rate along `(-1,16)`. -/
theorem seed_corner_nonstationary :
    (0 : Vec 2) ∉
        ConvexSubdifferential.subdifferential (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD) 0 ∧
      ∀ t : ℝ, 0 ≤ t → SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (t • ![-1, 16]) = -t := by
  have hray : ∀ t : ℝ, 0 ≤ t → SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (t • ![-1, 16]) = -t :=
    fun t ht => DEmbedding.seed_descent_ray ht
  refine ⟨fun h => ?_, hray⟩
  have h1 := h ((1 : ℝ) • ![-1, 16])
  have h0 := hray 0 le_rfl
  rw [zero_smul] at h0
  rw [hray 1 zero_le_one, h0] at h1
  simp [dot] at h1
  linarith

/-- Item `A/geometry/prose/010` (`paper/sections/geometry.tex:24-26`), caption of Figure
`art:gradient-geometry`: "the particular three-gradient seed used in
Section~\ref{art:failure}. Its convex hull excludes zero, but its affine hull is
the plane." -/
theorem seed_hulls :
    (0 : Vec 2) ∉ convexHull ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) ∧
      affineSpan ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) = ⊤ :=
  ⟨ArticleGeometry.seed_convex_hull_excludes_zero, ArticleGeometry.seed_affine_span_top⟩

/-! ## Affine and convex balance of a finite slope family -/

section Balance

/-- Item `A/geometry/prose/019` (`paper/sections/geometry.tex:44-46`): for a nonempty
finite family of slopes `a_i`, "equality $a_i^Tv=\kappa<0$ for every $i$ asks for a
common rate of descent ... The former fails when zero belongs to their affine
hull". -/
theorem common_rate_fails_of_mem_affineSpan {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (range a)) :
    ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (κ : ℝ), κ < 0 ∧ ∀ i, ⟪a i, v⟫_ℝ = κ := fun h =>
  (ArticleGeometry.affine_negative_common_rate_iff a (Classical.arbitrary ι)).mp h h0

/-- Item `A/geometry/prose/020` (`paper/sections/geometry.tex:45-47`): "$a_i^Tv<0$ asks
only for descent ... the latter fails when zero belongs to their convex hull." -/
theorem descent_fails_of_mem_convexHull {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (range a)) :
    ¬ ∃ v : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, v⟫_ℝ < 0 := fun h =>
  (ArticleGeometry.finite_slopes_common_descent_iff a).mp h h0

/-- Item `A/geometry/prose/021` (`paper/sections/geometry.tex:47-48`): "Indeed, a linear
functional constant on the slopes is constant on their affine hull." -/
theorem constant_on_affineSpan {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) (h : ∀ i, ⟪a i, v⟫_ℝ = c) :
    ∀ z ∈ affineSpan ℝ (range a), ⟪z, v⟫_ℝ = c :=
  AffineCriticalGeometry.affine_pairing_of_constant a v c h

/-- Item `A/geometry/prose/022` (`paper/sections/geometry.tex:48-50`): "Conversely, if zero
is outside that affine hull, its nearest point gives a separating functional
constant on the hull; changing its sign gives the negative common value." The
nearest point `p` of the affine hull to zero satisfies `z^T p = ‖p‖^2 > 0` on the
hull, and `v=-p` gives `a_i^T v = -‖p‖^2 < 0` for every `i`. -/
theorem nearest_point_common_rate {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (range a)) :
    ∃ p ∈ affineSpan ℝ (range a),
      (∀ z ∈ affineSpan ℝ (range a), ‖p‖ ≤ ‖z‖) ∧ 0 < ‖p‖ ^ 2 ∧
      (∀ z ∈ affineSpan ℝ (range a), ⟪z, p⟫_ℝ = ‖p‖ ^ 2) ∧
      ∀ i, ⟪a i, -p⟫_ℝ = -‖p‖ ^ 2 := by
  set s := affineSpan ℝ (range a) with hs
  haveI : Nonempty s := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨a i, subset_affineSpan ℝ _ (mem_range_self i)⟩⟩
  set p : EuclideanSpace ℝ (Fin n) := ↑(EuclideanGeometry.orthogonalProjection s 0) with hp
  have hps : p ∈ s := EuclideanGeometry.orthogonalProjection_mem 0
  have horth := EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal s
    (0 : EuclideanSpace ℝ (Fin n))
  rw [← hp] at horth
  have hconst : ∀ z ∈ s, ⟪z, p⟫_ℝ = ‖p‖ ^ 2 := by
    intro z hz
    have hdir : z -ᵥ p ∈ s.direction := AffineSubspace.vsub_mem_direction hz hps
    have h := (Submodule.mem_orthogonal _ _).mp horth _ hdir
    simp only [vsub_eq_sub, zero_sub, inner_neg_right, neg_eq_zero, inner_sub_left] at h
    rw [← real_inner_self_eq_norm_sq]
    linarith
  have hne : p ≠ 0 := fun h => h0 (h ▸ hps)
  have hpos : 0 < ‖p‖ ^ 2 := by positivity
  refine ⟨p, hps, fun z hz => ?_, hpos, hconst, fun i => ?_⟩
  · have hz2 : ‖z‖ ^ 2 = ‖p‖ ^ 2 + ‖z - p‖ ^ 2 := by
      have hc := hconst z hz
      rw [norm_sub_sq_real, hc]
      ring
    have : ‖p‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z - p‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  · rw [inner_neg_right, hconst _ (subset_affineSpan ℝ _ (mem_range_self i))]

/-- Item `A/geometry/prose/023` (`paper/sections/geometry.tex:51-52`): "The convex version
follows from the same closest-point argument for the convex hull." If zero is
outside the convex hull, its nearest point `p` in the hull satisfies
`z^T p ≥ ‖p‖^2 > 0` on the hull, so `v=-p` is a common strict descent direction. -/
theorem closest_point_descent {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ convexHull ℝ (range a)) :
    ∃ p ∈ convexHull ℝ (range a),
      (∀ z ∈ convexHull ℝ (range a), ‖p‖ ≤ ‖z‖) ∧ 0 < ‖p‖ ^ 2 ∧
      (∀ z ∈ convexHull ℝ (range a), ‖p‖ ^ 2 ≤ ⟪z, p⟫_ℝ) ∧
      ∀ i, ⟪a i, -p⟫_ℝ < 0 := by
  set K := convexHull ℝ (range a) with hK
  have hKc : IsCompact K := (Set.finite_range a).isCompact_convexHull
  have hKne : K.Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨a i, subset_convexHull ℝ _ (mem_range_self i)⟩
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  obtain ⟨p, hpK, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete hconv
    (0 : EuclideanSpace ℝ (Fin n))
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hpK).mp hpmin
  have hlow : ∀ z ∈ K, ‖p‖ ^ 2 ≤ ⟪z, p⟫_ℝ := by
    intro z hz
    have h := hvar z hz
    simp only [zero_sub, inner_neg_left, inner_sub_right] at h
    rw [← real_inner_self_eq_norm_sq]
    have hcomm := real_inner_comm p z
    linarith
  have hne : p ≠ 0 := fun h => h0 (h ▸ hpK)
  have hpos : 0 < ‖p‖ ^ 2 := by positivity
  refine ⟨p, hpK, fun z hz => ?_, hpos, hlow, fun i => ?_⟩
  · have hz := hlow z hz
    have hcs := real_inner_le_norm z p
    have : ‖p‖ ^ 2 ≤ ‖z‖ * ‖p‖ := hz.trans hcs
    have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hne
    nlinarith
  · rw [inner_neg_right]
    have := hlow _ (subset_convexHull ℝ _ (mem_range_self i))
    linarith

end Balance

/-! ## Table `art:positive-outcomes` -/

/-- Item `A/geometry/prose/031` (`paper/sections/geometry.tex:84-85`), caption of Table
`art:positive-outcomes`: "The benchmark $u^2+|v|$ has compact sublevels
everywhere, so the first row gives global convergence." Every sublevel of
`F(u,v)=u^2+|v|` is compact, and every infinite admissible run converges to the
minimizer in value and iterates. -/
theorem benchmark_compact_sublevels_global :
    (∀ b : ℝ, IsCompact {x : Vec 2 | UnexcitedMetric.objective x ≤ b}) ∧
      ∀ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective,
        Tendsto (fun k => UnexcitedMetric.objective (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) := by
  have hmin : ∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x := by
    intro x
    simpa [UnexcitedMetric.objective] using UnexcitedMetric.objective_nonneg x
  have hu : ∀ x, UnexcitedMetric.objective x = UnexcitedMetric.objective 0 → x = 0 :=
    fun _ hx => UnexcitedMetric.unique_minimum hx
  exact ⟨Localization.sublevel_compact UnexcitedMetric.objective_convex 0 hmin hu,
    ArticlePositive.mixed_benchmark_global⟩

end BfgsCoverage.Article.Geometry
