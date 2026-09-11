import BfgsVerification.CenteredCocoercivity

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix
namespace BfgsVerification.ConstantRankFields
open CenteredSmoothSublinear

/-- The actual local descent test gives a uniform one-sided Bregman estimate
on a compact subset of a convex C1,1 chart. The test point is proved to remain
in the larger chart; no global smoothness or assumed descent inequality is used. -/
theorem exists_one_sided_constant_on_compact {n : ℕ} {ψ : Vec n → ℝ}
    {U K : Set (Vec n)} (hU : IsOpen U) (hconvex : ConvexOn ℝ U ψ)
    (hsmooth : LocallyC11On U ψ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      sqNorm (coordinateGradient ψ y - coordinateGradient ψ x) ≤
        2 * L * (ψ y-ψ x-dot (coordinateGradient ψ x) (y-x)) := by
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
  exact ⟨L,hL,hbreg⟩

end BfgsVerification.ConstantRankFields
