import BfgsVerification.ConvexDifferentiability
import BfgsVerification.InwardRadial

/-! Boundary-safe jointly differentiable inward approximations on the original
sublevel. Positive-band membership is preserved by an open value margin. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace RadialCertificate

theorem inwardPoint_eq_homothety {n : ℕ} (star x : Vec n) (t : ℝ) :
    inwardPoint star x t = AffineMap.homothety star (1 - t) x := by
  simp only [inwardPoint, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  module

theorem continuous_inwardPoint {n : ℕ} (star : Vec n) (t : ℝ) :
    Continuous (fun x : Vec n => inwardPoint star x t) := by
  unfold inwardPoint
  fun_prop

theorem inwardPoint_eq_combo {n : ℕ} (star x : Vec n) (t : ℝ) :
    inwardPoint star x t = (1 - t) • x + t • star := by
  unfold inwardPoint
  module

/-- Convexity and the attained minimum order every inward pair. -/
theorem inward_value_le {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (x : Vec n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : F (inwardPoint star x t) ≤ F x := by
  have hc := hF.2 (show x ∈ univ by trivial) (show star ∈ univ by trivial)
    (sub_nonneg.mpr ht1) ht0 (show (1 - t) + t = 1 by ring)
  rw [← inwardPoint_eq_combo] at hc
  simp only [smul_eq_mul] at hc
  nlinarith [mul_le_mul_of_nonneg_left (hmin x) ht0]

/-- The original outer supporting plane supplies the source GR value-drop
bound without requiring differentiability of the inner endpoint. -/
theorem inward_value_lower {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star x g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (G R : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hgn : sqNorm g ≤ G ^ 2) (hxn : sqNorm (x - star) ≤ R ^ 2)
    {t : ℝ} (ht : 0 ≤ t) : F x - t * (G * R) ≤ F (inwardPoint star x t) := by
  have hs := supportingError_nonneg hF hg (inwardPoint star x t)
  rw [inward_error_eq] at hs
  have hd : dot g (x - star) ≤ G * R :=
    (le_abs_self _).trans (abs_dot_le_of_sqNorm_le g (x - star) G R hG hR hgn hxn)
  nlinarith [mul_le_mul_of_nonneg_left hd ht]

/-- The source's spare η/4 margin is valid even at a nondifferentiable inner point. -/
theorem inward_positive_band_margin {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star x g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (G R η : ℝ) (hG : 0 < G) (hR : 0 < R)
    (hgn : sqNorm g ≤ G ^ 2) (hxn : sqNorm (x - star) ≤ R ^ 2)
    (hband : F star + η ≤ F x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ η / (4 * G * R)) :
    F star + 3 * η / 4 ≤ F (inwardPoint star x t) := by
  have hdrop := inward_value_lower hF star x g hg G R hG.le hR.le hgn hxn ht0
  have hden : 0 < 4 * G * R := by positivity
  have hprod := (le_div_iff₀ hden).mp ht
  nlinarith

/-- Joint density uses almost-everywhere differentiability of two actual
finite convex functions, followed by the inverse affine chain rule. -/
theorem dense_inward_differentiable_pairs {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {t : ℝ} (ht : t ≠ 1) :
    Dense {x : Vec n | DifferentiableAt ℝ F x ∧
      DifferentiableAt ℝ F (inwardPoint star x t)} := by
  simpa only [inwardPoint_eq_homothety] using
    dense_homothety_differentiable_pairs hF star (sub_ne_zero.mpr (Ne.symm ht))

/-- Every point of the sublevel can be approached from its interior while
retaining any open condition true at that point and joint endpoint differentiability. -/
theorem exists_inward_pair_approximation {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (b : ℝ) (hb : F star < b)
    (x : Vec n) (hx : F x ≤ b) {O : Set (Vec n)} (hO : IsOpen O) (hxO : x ∈ O)
    {t : ℝ} (ht : t ≠ 1) :
    ∃ u : ℕ → Vec n, Tendsto u atTop (𝓝 x) ∧
      ∀ j, u j ∈ interior {w | F w ≤ b} ∧ u j ∈ O ∧
        DifferentiableAt ℝ F (u j) ∧ DifferentiableAt ℝ F (inwardPoint star (u j) t) := by
  let K := {w : Vec n | F w ≤ b}
  let D := {w : Vec n | DifferentiableAt ℝ F w ∧ DifferentiableAt ℝ F (inwardPoint star w t)}
  have hc := convex_continuous hF
  have hKclosed : IsClosed K := isClosed_le hc continuous_const
  have hKconvex : Convex ℝ K := by simpa only [mem_univ, true_and] using hF.convex_le b
  have hstar : star ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    have hopen : IsOpen {w : Vec n | F w < b} := isOpen_lt hc continuous_const
    have hmem : {w : Vec n | F w < b} ∈ 𝓝 star := hopen.mem_nhds hb
    exact Filter.mem_of_superset hmem (fun w (hw : F w < b) => show w ∈ K from hw.le)
  have hxclosure : x ∈ closure (interior K) := by
    rw [hKconvex.closure_interior_eq_closure_of_nonempty_interior ⟨star, hstar⟩,
      hKclosed.closure_eq]
    exact hx
  have hOS : IsOpen (interior K ∩ O) := isOpen_interior.inter hO
  have hxOS : x ∈ closure (interior K ∩ O) := hO.closure_inter ⟨hxclosure, hxO⟩
  have hD : Dense D := dense_inward_differentiable_pairs hF star ht
  have hxgood : x ∈ closure ((interior K ∩ O) ∩ D) := by
    simpa only [closure_closure] using closure_mono (hD.open_subset_closure_inter hOS) hxOS
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hxgood
  exact ⟨u, hux, fun j => ⟨(hu j).1.1, (hu j).1.2, (hu j).2⟩⟩

end RadialCertificate
end BfgsVerification
