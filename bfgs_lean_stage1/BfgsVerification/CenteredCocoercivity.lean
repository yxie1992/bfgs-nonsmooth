import BfgsVerification.CenteredLocalUniform

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace CenteredSmoothSublinear

theorem sqNorm_smul {n : ℕ} (c : ℝ) (v : Vec n) :
    sqNorm (c • v) = c ^ 2 * sqNorm v := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem dot_self_eq_sqNorm {n : ℕ} (v : Vec n) : dot v v = sqNorm v := by
  simp only [dot, dotProduct, sqNorm, pow_two]

/-- The local descent test produces one Bregman lower bound. No division by a
secant curvature or nonzero gradient difference is needed. -/
theorem bregman_lower_of_descent {n : ℕ} (ψ : Vec n → ℝ) (p q x y : Vec n)
    (L : ℝ) (hL : 0 < L)
    (hsupport : dot p (y - L⁻¹ • (q - p) - x) ≤ ψ (y - L⁻¹ • (q - p)) - ψ x)
    (htaylor : ψ (y - L⁻¹ • (q - p)) - ψ y - dot q (-L⁻¹ • (q - p)) ≤
      L / 2 * sqNorm (-L⁻¹ • (q - p))) :
    sqNorm (q - p) ≤ 2 * L * (ψ y - ψ x - dot p (y - x)) := by
  let u := q - p
  have hz : y - L⁻¹ • (q - p) - x = (y - x) + (-L⁻¹) • (q - p) := by
    simp only [neg_smul]
    abel
  rw [hz] at hsupport
  change dotProduct p ((y - x) + (-L⁻¹) • u) ≤ _ at hsupport
  rw [dotProduct_add, dotProduct_smul] at hsupport
  change _ - _ - dotProduct q ((-L⁻¹) • u) ≤ _ at htaylor
  rw [dotProduct_smul, sqNorm_smul] at htaylor
  simp only [smul_eq_mul] at hsupport htaylor
  change _ ≤ L / 2 * ((-L⁻¹) ^ 2 * sqNorm u) at htaylor
  have hdot : dotProduct q u - dotProduct p u = sqNorm u := by
    rw [← sub_dotProduct]
    exact dot_self_eq_sqNorm u
  have hmul : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have he : (2 * L) * ((-L⁻¹) * (dotProduct q u - dotProduct p u) +
      (L / 2) * (-L⁻¹) ^ 2 * sqNorm u) = -sqNorm u := by
    rw [hdot]
    field_simp
    <;> ring
  have hs : (-L⁻¹) * (dotProduct q u - dotProduct p u) +
      (L / 2) * (-L⁻¹) ^ 2 * sqNorm u +
      (ψ y - ψ x - dot p (y - x)) ≥ 0 := by
    change _ + (_ - _ - dotProduct p (y - x)) ≥ 0
    nlinarith [hsupport, htaylor]
  have hm := mul_nonneg (show 0 ≤ 2 * L by positivity) hs
  nlinarith [he]


/-- Local C1,1 regularity and compactness derive a uniform Euclidean
cocoercivity constant. Convexity outside the given open neighborhood is absent. -/
theorem exists_cocoercivity_constant_on_compact {n : ℕ} {ψ : Vec n → ℝ}
    {U K : Set (Vec n)} (hU : IsOpen U) (hconvex : ConvexOn ℝ U ψ)
    (hsmooth : LocallyC11On U ψ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      sqNorm (coordinateGradient ψ y - coordinateGradient ψ x) ≤
        L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x) := by
  obtain ⟨M, ρ, hρ, hballs⟩ := compact_uniform_local_lipschitz hU hK hKU hsmooth.2
  obtain ⟨G, hG, hbound⟩ := compact_coordinateGradient_bound hsmooth.2 hK hKU
  let L : ℝ := max (2 * (M : ℝ)) (2 * G / ρ) + 1
  have hLM : 2 * (M : ℝ) ≤ L := by dsimp [L]; linarith [le_max_left (2 * (M : ℝ)) (2 * G / ρ)]
  have hL : 0 < L := by dsimp [L]; linarith [le_max_left (2 * (M : ℝ)) (2 * G / ρ), M.coe_nonneg]
  have hLρ : L⁻¹ * (2 * G) < ρ := by
    have hh : 2 * G / ρ < L := by dsimp [L]; linarith [le_max_right (2 * (M : ℝ)) (2 * G / ρ)]
    have hh' : 2 * G < L * ρ := (div_lt_iff₀ hρ).mp hh
    have hdiv : 2 * G / L < ρ := (div_lt_iff₀ hL).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ ψ x := fun x hx =>
    (hsmooth.1 x hx).differentiableAt (hU.mem_nhds hx)
  have htaylor : ∀ x ∈ K, ∀ z ∈ ball x ρ,
      ψ z - ψ x - dot (coordinateGradient ψ x) (z - x) ≤ L / 2 * sqNorm (z - x) := by
    intro x hx z hz
    have ht := taylor_remainder_le (convex_ball x ρ)
      (fun w hw => hdiff w ((hballs x hx).1 hw)) (hballs x hx).2 (mem_ball_self hρ) hz
    have hfc : fderiv ℝ ψ x = gradientFunctional (coordinateGradient ψ x) :=
      (gradientFunctional_coordinates (fderiv ℝ ψ x)).symm
    rw [hfc, gradientFunctional_apply] at ht
    exact (le_abs_self _).trans (ht.trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [mul_comm] using hLM)) (sqNorm_nonneg _)))
  have hbreg : ∀ x ∈ K, ∀ y ∈ K,
      sqNorm (coordinateGradient ψ y - coordinateGradient ψ x) ≤
        2 * L * (ψ y - ψ x - dot (coordinateGradient ψ x) (y - x)) := by
    intro x hx y hy
    let p := coordinateGradient ψ x
    let q := coordinateGradient ψ y
    have hnorm : ‖q - p‖ ≤ 2 * G := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      exact (pi_norm_sq_le_sqNorm _).trans (sqNorm_difference_le_four q p G (hbound y hy) (hbound x hx))
    have hsmall : ‖(-L⁻¹) • (q - p)‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hL)]
      exact (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hL.le)).trans_lt hLρ
    have hzy : y - L⁻¹ • (q - p) - y = (-L⁻¹) • (q - p) := by
      rw [neg_smul]
      abel
    have hz : y - L⁻¹ • (q - p) ∈ ball y ρ := by
      simpa only [mem_ball, dist_eq_norm, hzy] using hsmall
    apply bregman_lower_of_descent ψ p q x y L hL
    · simpa only [gradientFunctional_apply] using
        supporting_inequality_on hconvex (hasFDerivAt_coordinateGradient (hdiff x (hKU hx)))
          (hKU hx) ((hballs y hy).1 hz)
    · simpa only [hzy] using htaylor y hy (y - L⁻¹ • (q - p)) hz
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have ha := hbreg x hx y hy
  have hb := hbreg y hy x hx
  have hs : sqNorm (coordinateGradient ψ x - coordinateGradient ψ y) =
      sqNorm (coordinateGradient ψ y - coordinateGradient ψ x) := by
    simp only [sqNorm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [hs] at hb
  have hd : dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x) =
      -dot (coordinateGradient ψ x) (y - x) - dot (coordinateGradient ψ y) (x - y) := by
    change dotProduct (coordinateGradient ψ y - coordinateGradient ψ x) (y - x) =
      -dotProduct (coordinateGradient ψ x) (y - x) - dotProduct (coordinateGradient ψ y) (x - y)
    rw [sub_dotProduct, show x - y = -(y - x) by abel, dotProduct_neg]
    ring
  rw [hd]
  nlinarith

end CenteredSmoothSublinear
end BfgsVerification
