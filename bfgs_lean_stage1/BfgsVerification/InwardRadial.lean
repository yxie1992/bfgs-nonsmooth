import BfgsVerification.RadialEquivalence
import BfgsVerification.RadialConvergence

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace RadialCertificate

/-- An inward fractional displacement toward the reference minimizer. -/
def inwardPoint {n : ℕ} (star x : Vec n) (t : ℝ) : Vec n := x - t • (x - star)

/-- Exact source (IR): inward Taylor error at differentiable positive-band
points; the sampled inner point is not required to be differentiable. -/
def HasInwardTaylorBounds {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (star : Vec n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g, x ∈ K → F star + η ≤ F x →
      HasFDerivAt F (gradientFunctional g) x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ supportingError F x g (inwardPoint star x t) ∧
        supportingError F x g (inwardPoint star x t) ≤ M / 2 * t ^ 2

theorem dot_sub_right {n : ℕ} (x y z : Vec n) : dot x (y - z) = dot x y - dot x z := by
  unfold dot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inward_error_eq {n : ℕ} (F : Vec n → ℝ) (star x g : Vec n) (t : ℝ) :
    supportingError F x g (inwardPoint star x t) =
      F (inwardPoint star x t) - F x + t * dot g (x - star) := by
  unfold supportingError
  have he : inwardPoint star x t - x = -t • (x - star) := by
    unfold inwardPoint
    module
  rw [he, dot_smul_right]
  ring

/-- The inward supporting-plane probe at z gives the signed radial estimate. -/
theorem inward_probe {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star x z g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (M t : ℝ)
    (hir : supportingError F z h (inwardPoint star z t) ≤ M / 2 * t ^ 2) :
    t * radialNumerator star z g h ≤ supportingError F x g z + M / 2 * t ^ 2 := by
  have hs := convex_supporting_inequality hF hg (inwardPoint star z t)
  rw [inward_error_eq] at hir
  have he : inwardPoint star z t - x = (z - x) - t • (z - star) := by
    unfold inwardPoint
    module
  rw [he, dot_sub_right, dot_smul_right] at hs
  unfold radialNumerator supportingError
  rw [dot_sub_left]
  linarith

/-- The exact scalar optimization used by source R's inward-to-secant proof. -/
theorem inward_probe_quadratic_bound {A B D M θ : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hD : 0 ≤ D) (hM : 0 ≤ M) (hθ : 0 < θ)
    (hprobe : ∀ t : ℝ, 0 ≤ t → t ≤ θ → t * A ≤ D + M / 2 * t ^ 2) :
    A ^ 2 ≤ max (2 * M) (2 * B / θ) * D := by
  by_cases hm : 0 < M ∧ A ≤ M * θ
  · have ht : A / M ≤ θ := (div_le_iff₀ hm.1).2 (by nlinarith [hm.2])
    have hp := hprobe (A / M) (div_nonneg hA hm.1.le) ht
    have he : M * (A / M) = A := mul_div_cancel₀ A hm.1.ne'
    have hbound : A ^ 2 ≤ 2 * M * D := by
      nlinarith [mul_le_mul_of_nonneg_left hp hm.1.le]
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD)
  · have hma : M * θ ≤ A := by
      by_cases hm0 : M = 0
      · simpa [hm0] using hA
      · have hmpos := lt_of_le_of_ne hM (Ne.symm hm0)
        have hn : ¬ A ≤ M * θ := fun hh => hm ⟨hmpos, hh⟩
        exact (lt_of_not_ge hn).le
    have hp := hprobe θ hθ.le le_rfl
    have hd : A * θ ≤ 2 * D := by
      nlinarith [mul_le_mul_of_nonneg_right hma hθ.le]
    have hb : A ^ 2 ≤ (2 * B / θ) * D := by
      have hB : 0 ≤ B := hA.trans hAB
      have hmul := mul_le_mul_of_nonneg_left hd hB
      have hsq := mul_le_mul_of_nonneg_right hAB (mul_nonneg hA hθ.le)
      have hcancel : (2 * B / θ) * θ = 2 * B := div_mul_cancel₀ _ hθ.ne'
      nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hD)

/-- Swapping the inward probe endpoints changes the radial numerator to T−N. -/
theorem radialNumerator_swap {n : ℕ} (star x z g h : Vec n) :
    radialNumerator star x h g = secantCurvature x z g h - radialNumerator star z g h := by
  unfold radialNumerator secantCurvature dot
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Source R's inward Taylor condition implies RS on the same compact domain.
Only the sampled endpoint carrying the Taylor expansion is differentiated. -/
theorem radial_of_inward_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec n)} (hK : IsCompact K) (star : Vec n)
    (hIR : HasInwardTaylorBounds F K star) : HasRadialSecantBounds F K star := by
  obtain ⟨G, hG, hg⟩ := convex_gradient_bound_on_compact hF hK
  obtain ⟨R, hR, hr⟩ := compact_sqNorm_radius hK star
  intro η hη
  obtain ⟨M, θ, hθ, hθhalf, hTaylor⟩ := hIR η hη
  let M' := max M 0
  let C := max (2 * M') (2 * (2 * G * R) / θ)
  have hM' : 0 ≤ M' := le_max_right _ _
  have hC : 0 ≤ C := (mul_nonneg (by norm_num) hM').trans (le_max_left _ _)
  refine ⟨C, ?_⟩
  intro x z g h hx hz hzband horder hdg hdh ht
  have hxband : F star + η ≤ F x := hzband.trans horder
  have hTaylor' (w a : Vec n) (hw : w ∈ K) (hwb : F star + η ≤ F w)
      (hda : HasFDerivAt F (gradientFunctional a) w) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ) :
      supportingError F w a (inwardPoint star w t) ≤ M' / 2 * t ^ 2 := by
    have hh := (hTaylor w a hw hwb hda t ht0 htθ).2
    have hMM : M ≤ M' := le_max_left _ _
    nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_right hMM (sq_nonneg t)]
  by_cases hN : 0 ≤ radialNumerator star z g h
  · have hB : radialNumerator star z g h ≤ 2 * G * R :=
      (le_abs_self _).trans (abs_radialNumerator_le_two_mul star z g h G R hG.le hR.le
        (hg x hx g hdg) (hg z hz h hdh) (hr z hz))
    have hb := inward_probe_quadratic_bound hN hB (supportingError_nonneg hF hdg z)
      hM' hθ (fun t ht0 htθ => inward_probe hF star x z g h hdg M' t
        (hTaylor' z h hz hzband hdh t ht0 htθ))
    exact hb.trans (mul_le_mul_of_nonneg_left (supportingError_le_curvature hF hdh) hC)
  · have hNneg : radialNumerator star z g h < 0 := lt_of_not_ge hN
    have hA : 0 ≤ radialNumerator star x h g := by
      rw [radialNumerator_swap star x z g h]
      linarith
    have hB : radialNumerator star x h g ≤ 2 * G * R :=
      (le_abs_self _).trans (abs_radialNumerator_le_two_mul star x h g G R hG.le hR.le
        (hg z hz h hdh) (hg x hx g hdg) (hr x hx))
    have hb := inward_probe_quadratic_bound hA hB (supportingError_nonneg hF hdh x)
      hM' hθ (fun t ht0 htθ => inward_probe hF star z x h g hdh M' t
        (hTaylor' x g hx hxband hdg t ht0 htθ))
    have hDT : supportingError F z h x ≤ secantCurvature x z g h := by
      rw [secantCurvature_eq_errors F]
      exact le_add_of_nonneg_left (supportingError_nonneg hF hdg z)
    have hlast := hb.trans (mul_le_mul_of_nonneg_left hDT hC)
    have hswap := radialNumerator_swap star x z g h
    have hsq : (radialNumerator star z g h) ^ 2 ≤ (radialNumerator star x h g) ^ 2 := by
      nlinarith
    exact hsq.trans hlast

/-- Exact radial contraction identities for an arbitrary gradient pair. -/
theorem inward_secant_identities {n : ℕ} (star x g h : Vec n) (t : ℝ) :
    secantCurvature x (inwardPoint star x t) g h = t * dot (g - h) (x - star) ∧
    radialNumerator star (inwardPoint star x t) g h = -(1 - t) * dot (g - h) (x - star) := by
  have hs : inwardPoint star x t - x = -t • (x - star) := by
    unfold inwardPoint
    module
  have hr : inwardPoint star x t - star = (1 - t) • (x - star) := by
    unfold inwardPoint
    module
  unfold secantCurvature radialNumerator
  rw [hs, hr, dot_smul_right, dot_smul_right, dot_sub_left, dot_sub_left]
  constructor <;> ring

/-- The reverse implication's quantitative estimate when both endpoints are
differentiable. The later approximation step must remove the inner derivative;
this lemma is not itself the full RS-to-IR theorem. -/
theorem inward_error_le_of_pair_radial {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star x g h : Vec n) (t C : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hC : 0 ≤ C)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) (inwardPoint star x t))
    (hRS : 0 < secantCurvature x (inwardPoint star x t) g h →
      (radialNumerator star (inwardPoint star x t) g h) ^ 2 ≤
        C * secantCurvature x (inwardPoint star x t) g h) :
    supportingError F x g (inwardPoint star x t) ≤ 4 * C * t ^ 2 := by
  by_cases htzero : t = 0
  · subst t
    simp [inwardPoint, supportingError, dot]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  have hid := inward_secant_identities star x g h t
  have hD := supportingError_nonneg hF hg (inwardPoint star x t)
  have hDT := supportingError_le_curvature hF hh (x := x) (g := g)
  rw [hid.1] at hDT
  have ha : 0 ≤ dot (g - h) (x - star) := by nlinarith
  by_cases hazero : dot (g - h) (x - star) = 0
  · rw [hazero, mul_zero] at hDT
    exact hDT.trans (by positivity)
  have hapos : 0 < dot (g - h) (x - star) := lt_of_le_of_ne ha (Ne.symm hazero)
  have hb := hRS (by rw [hid.1]; exact mul_pos htpos hapos)
  rw [hid.1, hid.2] at hb
  have hdiv : (1 - t) ^ 2 * dot (g - h) (x - star) ≤ C * t := by
    apply (mul_le_mul_right hapos).mp
    nlinarith
  have hquarter : (1 / 4 : ℝ) ≤ (1 - t) ^ 2 := by nlinarith
  have hbound : dot (g - h) (x - star) ≤ 4 * C * t := by
    nlinarith [mul_le_mul_of_nonneg_right hquarter ha]
  nlinarith [mul_le_mul_of_nonneg_left hbound ht0]

end RadialCertificate
end BfgsVerification
