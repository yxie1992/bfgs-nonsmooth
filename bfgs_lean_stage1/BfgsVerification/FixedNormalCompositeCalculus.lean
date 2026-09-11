import BfgsVerification.CenteredRecentering
import BfgsVerification.FixedNormalVisibility

/-! Actual subgradient splitting for the smooth-plus-univariate family. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix
namespace BfgsVerification.FixedNormal
open CenteredSmoothSublinear

/-- Subtracting a smooth summand from an actual support is justified using
convexity of the remainder. Full objective differentiability is not assumed. -/
theorem supporting_remainder_of_smooth_sum {n : ℕ} {F ψ κ : Vec n → ℝ}
    (hκ : ConvexOn ℝ univ κ) {Ω : Set (Vec n)} (hΩ : IsOpen Ω)
    (hrep : ∀ x ∈ Ω, F x = ψ x + κ x) {x g p : Vec n} (hx : x ∈ Ω)
    (hg : Homogeneous.Supports F x g) (hp : HasFDerivAt ψ (gradientFunctional p) x) :
    Homogeneous.Supports κ x (g - p) := by
  intro z
  let d := z - x
  let q : ℝ → ℝ := fun t => ψ (x + t • d) + t * (κ z - κ x) - t * dot g d
  have ht : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hd : HasDerivAt q (dot p d + (κ z - κ x) - dot g d) 0 := by
    have hc := hp.comp_hasDerivAt_of_eq 0 ht (by simp)
    simpa only [q, gradientFunctional_apply, one_mul] using
      (hc.add ((hasDerivAt_id (0 : ℝ)).mul_const (κ z - κ x))).sub
        ((hasDerivAt_id (0 : ℝ)).mul_const (dot g d))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ Ω ∧ t < 1 := by
    have hc : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    have hlim : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by simpa using hc.tendsto 0
    exact (hlim.eventually (hΩ.mem_nhds hx)).and (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hlocal : IsLocalMinOn q (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with t ht0 htΩ
    have hc := hκ.2 (show x ∈ univ by trivial) (show z ∈ univ by trivial)
      (by linarith : 0 ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
    have he : (1 - t) • x + t • z = x + t • d := by dsimp [d]; module
    rw [he] at hc
    simp only [smul_eq_mul] at hc
    have hs := hg (x + t • d)
    rw [hrep _ htΩ.1, hrep x hx, add_sub_cancel_left, dot_smul_right] at hs
    simp only [q, zero_smul, add_zero, zero_mul, sub_zero]
    nlinarith
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Ici_self
  have hn := hlocal.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hcone
  have hn' : 0 ≤ dot p d + (κ z - κ x) - dot g d := by simpa using hn
  change (g - p) ⬝ᵥ d ≤ κ z - κ x
  rw [sub_dotProduct]
  simp only [dot, dotProduct] at hn' ⊢
  linarith

/-- Convexity of the scalar summand lifts through its actual affine normal
coordinate. -/
theorem convex_normal_composite {n : ℕ} {h : ℝ → ℝ}
    (hh : ConvexOn ℝ univ h) (a : Vec n) (b : ℝ) :
    ConvexOn ℝ univ (fun x => h (normalCoordinate a b x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ r s hr hs hrs
  have he : normalCoordinate a b (r • x + s • z) =
      r * normalCoordinate a b x + s * normalCoordinate a b z := by
    change a ⬝ᵥ (r • x + s • z) - b = r * (a ⬝ᵥ x - b) + s * (a ⬝ᵥ z - b)
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    have hsum : r * b + s * b = b := by rw [← add_mul, hrs, one_mul]
    nlinarith
  change h (normalCoordinate a b (r • x + s • z)) ≤ r * h (normalCoordinate a b x) + s * h (normalCoordinate a b z)
  rw [he]
  exact hh.2 (mem_univ _) (mem_univ _) hr hs hrs

/-- Every actual support of a normal-only function is parallel to the normal.
The scalar function need not be differentiable at the normal coordinate. -/
theorem normal_support_tangent_zero {n : ℕ} (h : ℝ → ℝ) {a : Vec n}
    (ha : sqNorm a = 1) (b : ℝ) {x p : Vec n}
    (hp : Homogeneous.Supports (fun y => h (normalCoordinate a b y)) x p) :
    tangentProjection a p = 0 := by
  let v := tangentProjection a p
  have hav : dot a v = 0 := tangentProjection_normal_zero ha p
  have he : normalCoordinate a b (x + v) = normalCoordinate a b x := by
    change a ⬝ᵥ (x + v) - b = a ⬝ᵥ x - b
    rw [dotProduct_add]
    change dot a x + dot a v - b = dot a x - b
    rw [hav, add_zero]
  have hs := hp (x + v)
  simp only [add_sub_cancel_left, he, sub_self] at hs
  have hd : dot p v = sqNorm p - (dot a p) ^ 2 := by
    change p ⬝ᵥ (p - dot a p • a) = sqNorm p - (dot a p) ^ 2
    rw [dotProduct_sub, dotProduct_smul]
    have hpp : p ⬝ᵥ p = sqNorm p := dot_self_eq_sqNorm p
    have hpa : p ⬝ᵥ a = dot a p := dotProduct_comm p a
    rw [hpp, hpa]
    simp only [smul_eq_mul]
    ring
  have hpy := tangentProjection_pythagorean ha p
  apply (CertificateGeometry.sqNorm_eq_zero_iff _).mp
  change sqNorm v = 0
  change sqNorm v + (dot a p) ^ 2 = sqNorm p at hpy
  nlinarith [sqNorm_nonneg v]

/-- The exact common tangential projection of every actual subgradient of a
locally represented smooth-plus-univariate objective. -/
theorem composite_support_projection {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hh : ConvexOn ℝ univ h) {Ω : Set (Vec n)} (hΩ : IsOpen Ω)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ)
    (hrep : ∀ y ∈ Ω, F y = ψ y + h (normalCoordinate a b y))
    {x g p : Vec n} (hx : x ∈ Ω) (hg : Homogeneous.Supports F x g)
    (hp : HasFDerivAt ψ (gradientFunctional p) x) :
    tangentProjection a g = tangentProjection a p := by
  have hκ := supporting_remainder_of_smooth_sum (convex_normal_composite hh a b)
    hΩ hrep hx hg hp
  have hz := normal_support_tangent_zero h ha b hκ
  change tangentMap a (g - p) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Monotonicity of the actual scalar contribution, derived from its supports. -/
theorem composite_secant_curvature_dominates {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hh : ConvexOn ℝ univ h) {Ω : Set (Vec n)} (hΩ : IsOpen Ω)
    (a : Vec n) (b : ℝ) (hrep : ∀ y ∈ Ω, F y = ψ y + h (normalCoordinate a b y))
    {x z g g' p p' : Vec n} (hx : x ∈ Ω) (hz : z ∈ Ω)
    (hg : Homogeneous.Supports F x g) (hg' : Homogeneous.Supports F z g')
    (hp : HasFDerivAt ψ (gradientFunctional p) x)
    (hp' : HasFDerivAt ψ (gradientFunctional p') z) :
    dot (p' - p) (z - x) ≤ dot (g' - g) (z - x) := by
  have hxκ := supporting_remainder_of_smooth_sum (convex_normal_composite hh a b) hΩ hrep hx hg hp z
  have hzκ := supporting_remainder_of_smooth_sum (convex_normal_composite hh a b) hΩ hrep hz hg' hp' x
  have he : x - z = -(z - x) := by abel
  change (g' - p') ⬝ᵥ (x - z) ≤ _ at hzκ
  rw [he, dotProduct_neg] at hzκ
  change (g - p) ⬝ᵥ (z - x) ≤ _ at hxκ
  change (p' - p) ⬝ᵥ (z - x) ≤ (g' - g) ⬝ᵥ (z - x)
  simp only [sub_dotProduct] at hxκ hzκ ⊢
  linarith

/-- The composite source's tangential strong convexity lifts to the full
objective from its scalar convex summand, on the same structural set. -/
theorem composite_projected_strong_convex {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    (hh : ConvexOn ℝ univ h) (a : Vec n) (b : ℝ) {Ω : Set (Vec n)} {μ : ℝ}
    (hstrong : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x)) :
    ConvexOn ℝ Ω (fun x => F x - (μ / 2) * sqNorm (tangentProjection a x)) := by
  apply (hstrong.add ((convex_normal_composite hh a b).subset (subset_univ _) hstrong.1)).congr
  intro x hx
  simp only [Pi.add_apply]
  rw [hrep x hx]
  ring

/-- U.17 with the exact original objective and arbitrary supporting endpoint
vectors. The smooth and scalar contributions, cocoercivity constant and scalar
monotonicity are all derived. -/
theorem exists_composite_tangent_secant {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω K : Set (Vec n)} (hΩ : IsOpen Ω) (hψ : ConvexOn ℝ Ω ψ)
    (hsmooth : LocallyC11On Ω ψ) (hh : ConvexOn ℝ univ h)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ z ∈ K, ∀ g g' : Vec n,
      Homogeneous.Supports F x g → Homogeneous.Supports F z g' →
      sqNorm (tangentProjection a (g' - g)) ≤ L * dot (g' - g) (z - x) := by
  obtain ⟨L, hL, hcoco⟩ := exists_cocoercivity_constant_on_compact hΩ hψ hsmooth hK hKΩ
  refine ⟨L, hL, ?_⟩
  intro x hx z hz g g' hg hg'
  let p := coordinateGradient ψ x
  let p' := coordinateGradient ψ z
  have hp : HasFDerivAt ψ (gradientFunctional p) x :=
    hasFDerivAt_coordinateGradient ((hsmooth.1 x (hKΩ hx)).differentiableAt (hΩ.mem_nhds (hKΩ hx)))
  have hp' : HasFDerivAt ψ (gradientFunctional p') z :=
    hasFDerivAt_coordinateGradient ((hsmooth.1 z (hKΩ hz)).differentiableAt (hΩ.mem_nhds (hKΩ hz)))
  have hxP := composite_support_projection hh hΩ ha b hrep (hKΩ hx) hg hp
  have hzP := composite_support_projection hh hΩ ha b hrep (hKΩ hz) hg' hp'
  have he : tangentProjection a (g' - g) = tangentProjection a (p' - p) := by
    change tangentMap a (g' - g) = tangentMap a (p' - p)
    rw [map_sub, map_sub]
    exact congrArg₂ (fun v w : Vec n => v - w) hzP hxP
  rw [he]
  exact (sqNorm_tangentProjection_le ha _).trans ((hcoco x hx z hz).trans
    (mul_le_mul_of_nonneg_left (composite_secant_curvature_dominates hh hΩ a b hrep
      (hKΩ hx) (hKΩ hz) hg hg' hp hp') hL.le))

end BfgsVerification.FixedNormal
