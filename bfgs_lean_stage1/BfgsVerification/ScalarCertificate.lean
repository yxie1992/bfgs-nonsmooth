import BfgsVerification.IncomingJumpObstruction
import BfgsVerification.ScalarConvergence

/-! Module G's exact scalar certificate characterization on eligible pairs.
The field uses actual derivatives, and the compact-band gradient bounds are
derived from finite convexity. There is no all-pair smoothness assumption. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter

namespace BfgsVerification.TransportedCertificate

theorem scalar_energy (W : Mat 1) (g : Vec 1) :
    metricEnergy W g = W 0 0 * (g 0) ^ 2 := by
  simp [metricEnergy, dot, Matrix.mulVec, dotProduct]
  ring

theorem scalar_projector_zero (s : Vec 1) (hs : s 0 ≠ 0) : stepProjector s = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [stepProjector, sqNorm, outer, pow_two, hs]
  field_simp

theorem EligiblePair.scalar_step_ne {F : Vec 1 → ℝ} {c₁ c₂ : ℝ}
    {x z g h : Vec 1} (e : EligiblePair F c₁ c₂ x z g h) : z 0 - x 0 ≠ 0 := by
  intro hs
  have he := e.decrease_pos
  simp [pairDecrease, pairStep, dot, hs] at he

theorem EligiblePair.scalar_curvature {F : Vec 1 → ℝ} {c₁ c₂ : ℝ}
    {x z g h : Vec 1} (e : EligiblePair F c₁ c₂ x z g h) (hc₂ : c₂ < 1) :
    0 < |h 0 - g 0| ∧
      pairCurvature x z g h = |h 0 - g 0| * |z 0 - x 0| := by
  have ht : 0 < pairCurvature x z g h :=
    (mul_pos (sub_pos.mpr hc₂) e.decrease_pos).trans_le e.curvature
  have heq : pairCurvature x z g h = (h 0 - g 0) * (z 0 - x 0) := by
    simp [pairCurvature, pairStep, dot]
  refine ⟨abs_pos.mpr ?_, ?_⟩
  · intro hy
    rw [heq, hy, zero_mul] at ht
    exact lt_irrefl _ ht
  · rw [← abs_mul, ← heq, abs_of_pos ht]

/-- The actual scalar derivative extracted from the Fréchet derivative. -/
def scalarGradient (F : Vec 1 → ℝ) (x : Vec 1) : ℝ :=
  fderiv ℝ F x (fun _ => 1)

theorem scalarGradient_eq {F : Vec 1 → ℝ} {x g : Vec 1}
    (hg : HasFDerivAt F (gradientFunctional g) x) : scalarGradient F x = g 0 := by
  rw [scalarGradient, hg.fderiv, gradientFunctional_apply]
  simp [dot]

theorem scalar_gradient_ne_zero {F : Vec 1 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 1) {K : Set (Vec 1)} {η : ℝ} (hη : 0 < η)
    {x g : Vec 1} (hx : x ∈ positiveBand F K (F star) η)
    (hg : HasFDerivAt F (gradientFunctional g) x) : g 0 ≠ 0 := by
  intro hzero
  have hs := convex_supporting_inequality hF hg star
  simp [dot, hzero] at hs
  have hb := hx.2
  linarith

/-- Source (G.scalar), written as a uniform bound rather than an extended-real
supremum; an empty eligible-pair collection is allowed. -/
def ScalarQuotientBound (F : Vec 1 → ℝ) (K : Set (Vec 1)) (fstar c₁ c₂ η : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ A : ℝ, ∀ x z g h,
    x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
    EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
    |h 0 - g 0| / (|z 0 - x 0| * (h 0) ^ 2) ≤ A

def ScalarEligibleLipschitz (F : Vec 1 → ℝ) (K : Set (Vec 1)) (fstar c₁ c₂ η : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ A : ℝ, ∀ x z g h,
    x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
    EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
    |h 0 - g 0| ≤ A * |z 0 - x 0|

/-- Visibility and suppression force the source scalar quotient bound. -/
theorem quotient_bound_of_visibility_secant {F : Vec 1 → ℝ} {K : Set (Vec 1)}
    {fstar c₁ c₂ η : ℝ} (hc₂ : c₂ < 1)
    (B : VisibilitySecantCertificate F K fstar c₁ c₂ η) :
    ScalarQuotientBound F K fstar c₁ c₂ η := by
  refine ⟨B.δ, B.delta_pos, B.C / B.m, ?_⟩
  intro x z g h hx hz e hd
  have hv := B.visibility z hz h e.gradient_z
  have hs := B.secant x z g h hx hz e hd
  rw [scalar_energy] at hv hs
  have hne : h 0 ≠ 0 := by intro hh; simp [hh] at hv; linarith [B.m_pos]
  obtain ⟨hy, ht⟩ := e.scalar_curvature hc₂
  have hstep : 0 < |z 0 - x 0| := abs_pos.mpr e.scalar_step_ne
  rw [ht] at hs
  have hprod : B.m * |h 0 - g 0| ≤ B.C * |z 0 - x 0| * (h 0) ^ 2 := by
    apply (mul_le_mul_right hy).mp
    have h1 := mul_le_mul_of_nonneg_right hv (sq_nonneg (h 0 - g 0))
    have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg (h 0))
    simp only [Pi.sub_apply] at h1 h2
    have h12 : B.m * (h 0 - g 0) ^ 2 ≤ B.C * (|h 0 - g 0| * |z 0 - x 0|) * (h 0) ^ 2 :=
      h1.trans (by convert h2 using 1 <;> ring)
    rw [← sq_abs (h 0 - g 0)] at h12
    convert h12 using 1 <;> ring
  apply (div_le_iff₀ (mul_pos hstep (sq_pos_of_ne_zero hne))).mpr
  apply (mul_le_mul_left B.m_pos).mp
  have hc : B.m * (B.C / B.m) = B.C := by field_simp [B.m_pos.ne']
  rw [← mul_assoc, hc]
  convert hprod using 1 <;> ring

/-- The inverse squared actual gradient is a finite PSD field realizing every
uniform scalar quotient bound; transport is identically zero. -/
def certificateOfScalarQuotient {F : Vec 1 → ℝ} {K : Set (Vec 1)}
    {fstar c₁ c₂ η : ℝ} (hc₂ : c₂ < 1)
    (hne : ∀ x ∈ positiveBand F K fstar η, ∀ g,
      HasFDerivAt F (gradientFunctional g) x → g 0 ≠ 0)
    (δ A : ℝ) (hδ : 0 < δ)
    (hQ : ∀ x z g h, x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
      EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
      |h 0 - g 0| / (|z 0 - x 0| * (h 0) ^ 2) ≤ A) :
    BandCertificate F K fstar c₁ c₂ η where
  W x := ((scalarGradient F x) ^ 2)⁻¹ • outer (fun _ => 1) (fun _ => 1)
  m := 1
  C := A
  L := 0
  δ := δ
  m_pos := zero_lt_one
  L_nonneg := le_refl _
  delta_pos := hδ
  positive_semidefinite x _ _ :=
    SmoothSubspace.scaled_outer_posSemidef _ _ (inv_nonneg.mpr (sq_nonneg _))
  visibility x hx g hg := by
    rw [scalar_energy, scalarGradient_eq hg]
    simp only [Matrix.smul_apply, smul_eq_mul, outer, mul_one]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 (hne x hx g hg))]
  secant x z g h hx hz e hd := by
    rw [scalar_energy, scalarGradient_eq e.gradient_z]
    simp only [Matrix.smul_apply, smul_eq_mul, outer, mul_one, Pi.sub_apply]
    obtain ⟨hy, ht⟩ := e.scalar_curvature hc₂
    have hhp := sq_pos_of_ne_zero (hne z hz h e.gradient_z)
    have hsp := abs_pos.mpr e.scalar_step_ne
    have hq := (div_le_iff₀ (mul_pos hsp hhp)).mp (hQ x z g h hx hz e hd)
    rw [ht]
    apply (mul_le_mul_left hhp).mp
    have hinv := mul_inv_cancel₀ hhp.ne'
    have hm := mul_le_mul_of_nonneg_right hq hy.le
    nlinarith [sq_abs (h 0 - g 0)]
  transport x z g h _ _ e _ := by
    rw [scalar_projector_zero (pairStep x z) e.scalar_step_ne]
    simpa using (Matrix.PosSemidef.zero : (0 : Mat 1).PosSemidef)

theorem scalar_certificate_iff_quotient {F : Vec 1 → ℝ} {K : Set (Vec 1)}
    (hF : ConvexOn ℝ univ F) (star : Vec 1) {c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (hη : 0 < η) :
    Nonempty (BandCertificate F K (F star) c₁ c₂ η) ↔
      ScalarQuotientBound F K (F star) c₁ c₂ η := by
  constructor
  · rintro ⟨B⟩
    exact quotient_bound_of_visibility_secant hc₂ B.toVisibilitySecant
  · rintro ⟨δ, hδ, A, hA⟩
    exact ⟨certificateOfScalarQuotient hc₂
      (fun _ hx _ hg => scalar_gradient_ne_zero hF star hη hx hg) δ A hδ hA⟩

/-- Compact positive bands provide both gradient bounds, without gradient
continuity or differentiability away from the tested endpoints. -/
theorem scalar_gradient_band_bounds {F : Vec 1 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 1) {K : Set (Vec 1)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ m G : ℝ, 0 < m ∧ 0 < G ∧ ∀ x ∈ positiveBand F K (F star) η, ∀ g,
      HasFDerivAt F (gradientFunctional g) x → m ≤ |g 0| ∧ |g 0| ≤ G := by
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 star
  obtain ⟨G, hG, hg⟩ := convex_gradient_bound_on_compact hF hK
  refine ⟨η / R, G, div_pos hη hR, hG, ?_⟩
  intro x hx g hdiff
  have hd : |x 0 - star 0| ≤ R := by
    calc
      _ ≤ ‖x - star‖ := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - star) 0
      _ = dist x star := (dist_eq_norm _ _).symm
      _ ≤ R := hsub hx.1
  have hs := convex_supporting_inequality hF hdiff star
  simp only [dot, Fin.sum_univ_one, Pi.sub_apply] at hs
  have hb := hx.2
  have hp : η ≤ g 0 * (x 0 - star 0) := by nlinarith
  have hpair : g 0 * (x 0 - star 0) ≤ |g 0| * R := by
    calc
      _ ≤ |g 0 * (x 0 - star 0)| := le_abs_self _
      _ = |g 0| * |x 0 - star 0| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  refine ⟨(div_le_iff₀ hR).mpr (hp.trans hpair), ?_⟩
  have hu := hg x hx.1 g hdiff
  simp only [sqNorm, Fin.sum_univ_one] at hu
  nlinarith [sq_abs (g 0), abs_nonneg (g 0)]

theorem scalar_quotient_iff_lipschitz_of_bounds {F : Vec 1 → ℝ} {K : Set (Vec 1)}
    {fstar c₁ c₂ η : ℝ} (m G : ℝ) (hm : 0 < m) (hG : 0 < G)
    (hgrad : ∀ x ∈ positiveBand F K fstar η, ∀ g,
      HasFDerivAt F (gradientFunctional g) x → m ≤ |g 0| ∧ |g 0| ≤ G) :
    ScalarQuotientBound F K fstar c₁ c₂ η ↔ ScalarEligibleLipschitz F K fstar c₁ c₂ η := by
  have hne : ∀ x ∈ positiveBand F K fstar η, ∀ g,
      HasFDerivAt F (gradientFunctional g) x → g 0 ≠ 0 := by
    intro x hx g hg he
    have hb := (hgrad x hx g hg).1
    simp [he] at hb
    linarith
  constructor
  · rintro ⟨δ, hδ, A, hA⟩
    refine ⟨δ, hδ, max A 0 * G ^ 2, ?_⟩
    intro x z g h hx hz e hd
    have hsp := abs_pos.mpr e.scalar_step_ne
    have hhp := sq_pos_of_ne_zero (hne z hz h e.gradient_z)
    have hq := (div_le_iff₀ (mul_pos hsp hhp)).mp ((hA x z g h hx hz e hd).trans (le_max_left A 0))
    have hu : (h 0) ^ 2 ≤ G ^ 2 := by
      have hbound := (hgrad z hz h e.gradient_z).2
      nlinarith [sq_abs (h 0), abs_nonneg (h 0)]
    calc
      _ ≤ max A 0 * (|z 0 - x 0| * (h 0) ^ 2) := hq
      _ ≤ max A 0 * (|z 0 - x 0| * G ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hsp.le) (le_max_right A 0)
      _ = _ := by ring
  · rintro ⟨δ, hδ, A, hA⟩
    refine ⟨δ, hδ, max A 0 / m ^ 2, ?_⟩
    intro x z g h hx hz e hd
    have hsp := abs_pos.mpr e.scalar_step_ne
    have hhp := sq_pos_of_ne_zero (hne z hz h e.gradient_z)
    have hlo : m ^ 2 ≤ (h 0) ^ 2 := by
      have hb := (hgrad z hz h e.gradient_z).1
      nlinarith [sq_abs (h 0), abs_nonneg (h 0)]
    calc
      _ ≤ (max A 0 * |z 0 - x 0|) / (|z 0 - x 0| * (h 0) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hsp hhp).le
        exact (hA x z g h hx hz e hd).trans (mul_le_mul_of_nonneg_right (le_max_left A 0) hsp.le)
      _ = max A 0 / (h 0) ^ 2 := by field_simp; ring
      _ ≤ max A 0 / m ^ 2 := div_le_div_of_nonneg_left (le_max_right A 0) (sq_pos_of_pos hm) hlo

/-- Exact source scalar characterization. Compactness and finite convexity
derive the gradient bounds needed to replace the quotient by eligible-pair
Lipschitz control. No condition on pairs outside eligibility is introduced. -/
theorem scalar_certificate_iff_eligible_lipschitz {F : Vec 1 → ℝ} {K : Set (Vec 1)}
    (hF : ConvexOn ℝ univ F) (star : Vec 1) (hK : IsCompact K) {c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (hη : 0 < η) :
    Nonempty (BandCertificate F K (F star) c₁ c₂ η) ↔
      ScalarEligibleLipschitz F K (F star) c₁ c₂ η := by
  obtain ⟨m, G, hm, hG, hb⟩ := scalar_gradient_band_bounds hF star hK hη
  exact (scalar_certificate_iff_quotient hF star hc₂ hη).trans
    (scalar_quotient_iff_lipschitz_of_bounds m G hm hG hb)

end BfgsVerification.TransportedCertificate
