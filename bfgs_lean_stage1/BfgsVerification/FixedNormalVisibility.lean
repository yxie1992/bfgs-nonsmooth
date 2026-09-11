import BfgsVerification.FixedNormalCutoff
import BfgsVerification.CenteredLocalUniform

/-! The cutoff-masked gradient is continuous even across exceptional points.
Uniform visibility is obtained on a neighborhood of the whole compact cluster set. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace FixedNormal

def normalCoordinate {n : ℕ} (a : Vec n) (b : ℝ) (x : Vec n) : ℝ := dot a x - b

def regularRegion {n : ℕ} (Ω : Set (Vec n)) (a : Vec n) (b : ℝ) (E : Set ℝ) : Set (Vec n) :=
  Ω ∩ {x | normalCoordinate a b x ∉ E}

theorem continuous_normalCoordinate {n : ℕ} (a : Vec n) (b : ℝ) :
    Continuous (normalCoordinate a b) := by
  unfold normalCoordinate dot
  fun_prop

theorem isOpen_regularRegion {n : ℕ} {Ω : Set (Vec n)} (hΩ : IsOpen Ω)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E) :
    IsOpen (regularRegion Ω a b E) :=
  hΩ.inter ((hE.preimage (continuous_normalCoordinate a b)).isOpen_compl)

def maskedNormalDerivative {n : ℕ} (F : Vec n → ℝ) (a : Vec n) (b : ℝ)
    (τ : ℝ → ℝ) (x : Vec n) : ℝ :=
  τ (normalCoordinate a b x) * dot a (coordinateGradient F x)

def visibilityFunction {n : ℕ} (F : Vec n → ℝ) (A : Vec n → Vec n)
    (a : Vec n) (b : ℝ) (τ : ℝ → ℝ) (x : Vec n) : ℝ :=
  sqNorm (A x) + (maskedNormalDerivative F a b τ x) ^ 2

/-- No continuity of the full gradient is asserted at exceptional points: the
normal term vanishes identically on a neighborhood of each such point. -/
theorem continuousOn_maskedNormalDerivative {n : ℕ} {F : Vec n → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (a : Vec n) (b : ℝ)
    {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} (hτ : Continuous τ) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) :
    ContinuousOn (maskedNormalDerivative F a b τ) Ω := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  by_cases he : normalCoordinate a b p ∈ E
  · have hclose : ∀ᶠ q in 𝓝 p,
        |normalCoordinate a b q - normalCoordinate a b p| < δ := by
      have hc := ((continuous_normalCoordinate a b).sub (continuous_const (y := normalCoordinate a b p))).abs
      have ht : Tendsto (fun q => |normalCoordinate a b q - normalCoordinate a b p|)
          (𝓝 p) (𝓝 0) := by simpa using hc.tendsto p
      exact ht.eventually_lt_const hδ
    apply (continuousAt_const : ContinuousAt (fun _ : Vec n => (0 : ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hclose] with q hq
    simp only [maskedNormalDerivative, hzero _ _ he hq.le, zero_mul]
  · have hreg := isOpen_regularRegion hΩ a b hE
    have hpreg : p ∈ regularRegion Ω a b E := ⟨hp, he⟩
    have hg := (CenteredSmoothSublinear.continuousOn_coordinateGradient hsmooth.2 p hpreg).continuousAt
      (hreg.mem_nhds hpreg)
    have hd : ContinuousAt (fun q => dot a (coordinateGradient F q)) p := by
      exact (continuous_dot.comp (continuous_const.prodMk continuous_id)).continuousAt.comp hg
    exact ((hτ.comp (continuous_normalCoordinate a b)).continuousAt).mul hd

/-- The actual source visibility expression is continuous across all interfaces. -/
theorem continuousOn_visibilityFunction {n : ℕ} {F : Vec n → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) {A : Vec n → Vec n} (hA : ContinuousOn A Ω)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} (hτ : Continuous τ) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) :
    ContinuousOn (visibilityFunction F A a b τ) Ω :=
  (continuous_sqNorm.comp_continuousOn hA).add
    ((continuousOn_maskedNormalDerivative hΩ a b hE hsmooth hτ hδ hzero).pow 2)

/-- A cutoff is selected from the entire compact tangential-zero set, never from
one presumed limiting point. -/
theorem exists_cutoff_for_compact_set {n : ℕ} {Ω Γ : Set (Vec n)}
    (hΓ : IsCompact Γ) (hΓΩ : Γ ⊆ Ω) {A : Vec n → Vec n} (hA : ContinuousOn A Ω)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E)
    (hdis : ∀ p ∈ Γ, A p = 0 → normalCoordinate a b p ∉ E) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ≥0, ∃ τ : ℝ → ℝ,
      LipschitzWith L τ ∧ (∀ t, 0 ≤ τ t ∧ τ t ≤ 1) ∧
      (∀ p ∈ Γ, A p = 0 → τ (normalCoordinate a b p) = 1) ∧
      (∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) := by
  let Z : Set (Vec n) := Γ ∩ A ⁻¹' {(0 : Vec n)}
  have hZ : IsCompact Z := hΓ.of_isClosed_subset
    ((hA.mono hΓΩ).preimage_isClosed_of_isClosed hΓ.isClosed isClosed_singleton) inter_subset_left
  have hrZ : IsCompact ((normalCoordinate a b) '' Z) := hZ.image (continuous_normalCoordinate a b)
  have hd : Disjoint ((normalCoordinate a b) '' Z) E := by
    apply Set.disjoint_left.mpr
    rintro t ⟨p, hp, rfl⟩ he
    exact hdis p hp.1 hp.2 he
  obtain ⟨δ, hδ, L, τ, hτ, hb, ho, hz⟩ := exists_separating_cutoff hE hrZ hd
  refine ⟨δ, hδ, L, τ, hτ, hb, ?_, hz⟩
  intro p hp hAp
  exact ho _ ⟨p, ⟨hp, hAp⟩, rfl⟩

/-- Positive visibility uses either a nonzero tangent field or, where it
vanishes, a restored nonzero actual gradient. -/
theorem visibilityFunction_pos {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {a : Vec n} (ha : sqNorm a = 1)
    {A : Vec n → Vec n} {x : Vec n} {b : ℝ} {τ : ℝ → ℝ}
    (hA : ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x)
    (hrestored : A x = 0 → τ (normalCoordinate a b x) = 1 ∧
      DifferentiableAt ℝ F x ∧ coordinateGradient F x ≠ 0) :
    0 < visibilityFunction F A a b τ x := by
  have hsqpos (v : Vec n) (hv : v ≠ 0) : 0 < sqNorm v :=
    lt_of_le_of_ne (sqNorm_nonneg v) (fun he => hv (CertificateGeometry.sqNorm_eq_zero_iff v |>.mp he.symm))
  by_cases hx : A x = 0
  · obtain ⟨ht, hdiff, hne⟩ := hrestored hx
    have hp := hA _ (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hdiff))
    have hpy := tangentProjection_pythagorean ha (coordinateGradient F x)
    rw [hp, hx] at hpy
    have hs := hsqpos _ hne
    simp only [sqNorm, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, zero_add] at hpy
    simpa only [visibilityFunction, maskedNormalDerivative, hx, ht, one_mul,
      sqNorm, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
      zero_add, ← hpy] using hs
  · exact add_pos_of_pos_of_nonneg (hsqpos _ hx) (sq_nonneg _)

/-- Compact positive visibility has one positive lower bound on an open
neighborhood of the entire compact set. -/
theorem exists_visibility_neighborhood {n : ℕ} {F : Vec n → ℝ}
    {A : Vec n → Vec n} {a : Vec n} {b : ℝ} {τ : ℝ → ℝ}
    {Ω Γ : Set (Vec n)} (hΩ : IsOpen Ω) (hΓ : IsCompact Γ) (hΓn : Γ.Nonempty)
    (hΓΩ : Γ ⊆ Ω) (hc : ContinuousOn (visibilityFunction F A a b τ) Ω)
    (hp : ∀ x ∈ Γ, 0 < visibilityFunction F A a b τ x) :
    ∃ m : ℝ, 0 < m ∧ ∃ N : Set (Vec n), IsOpen N ∧ Γ ⊆ N ∧ N ⊆ Ω ∧
      ∀ x ∈ N, m ≤ visibilityFunction F A a b τ x := by
  obtain ⟨p, hpΓ, hmin⟩ := hΓ.exists_isMinOn hΓn (hc.mono hΓΩ)
  let m := visibilityFunction F A a b τ p / 2
  have hm : 0 < m := by dsimp [m]; exact half_pos (hp p hpΓ)
  let N := Ω ∩ (visibilityFunction F A a b τ) ⁻¹' Ioi m
  refine ⟨m, hm, N, hc.isOpen_inter_preimage hΩ isOpen_Ioi, ?_, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hΓΩ hx, ?_⟩
    have hb := hmin hx
    change visibilityFunction F A a b τ p ≤ visibilityFunction F A a b τ x at hb
    change m < visibilityFunction F A a b τ x
    dsimp [m]
    linarith [hp p hpΓ]
  · intro x hx
    exact hx.2.le

/-- At differentiable accepted points the continuous scalar visibility is
exactly the actual frame-gradient pairing. -/
theorem cutoffFrame_pairing_eq_visibility {n r : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {A : Vec n → Vec n} {a : Vec n} {b : ℝ} {τ : ℝ → ℝ}
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = tangentProjection a v)
    {x g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x)
    (hA : ∀ h, Homogeneous.Supports F x h → tangentProjection a h = A x) :
    sqNorm ((cutoffFrame U a (τ (normalCoordinate a b x)))ᵀ.mulVec g) =
      visibilityFunction F A a b τ x := by
  have he : coordinateGradient F x = g := supporting_vector_eq_gradient
    (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hg.differentiableAt)) hg
  rw [cutoffFrame_pairing, tangent_matrix_sqNorm a U hU hproj,
    hA _ (convex_supporting_inequality hF hg)]
  simp only [visibilityFunction, maskedNormalDerivative, he, mul_pow]

end FixedNormal
end BfgsVerification
