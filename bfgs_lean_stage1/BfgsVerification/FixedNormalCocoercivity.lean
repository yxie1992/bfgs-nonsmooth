import BfgsVerification.CenteredCocoercivity
import BfgsVerification.FixedNormalSmoothStrip

/-! A smooth-chart extension needed for the tangential-only U.6 argument. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix
namespace BfgsVerification.FixedNormal
open CenteredSmoothSublinear

/-- For a globally convex objective, local C1,1 on an arbitrary open set gives
uniform Euclidean cocoercivity between points of a compact subset. The smooth
open set need not be convex or connected; the supporting inequalities use the
actual global objective. -/
theorem exists_cocoercivity_constant_on_smooth_compact {n : ℕ} {ψ : Vec n → ℝ}
    {U K : Set (Vec n)} (hU : IsOpen U) (hconvex : ConvexOn ℝ univ ψ)
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
        convex_supporting_inequality hconvex (hasFDerivAt_coordinateGradient (hdiff x (hKU hx)))
          (y - L⁻¹ • (q - p))
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

/-- The exact late-pair estimate in a nonzero cutoff strip, without a positive
lower bound on full curvature. Only objective convexity and local C1,1 off the
closed exceptional levels are used. -/
theorem exists_cutoff_strip_cocoercivity {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {Ω K : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : LocallyC11On (regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ K, ∀ z ∈ K, τ (normalCoordinate a b z) ≠ 0 → ‖z - x‖ < ρ →
        sqNorm (coordinateGradient F z - coordinateGradient F x) ≤
          C * dot (coordinateGradient F z - coordinateGradient F x) (z - x) := by
  let D : Set (Vec n) := {z | ∀ e ∈ E, δ / 2 ≤ |normalCoordinate a b z - e|}
  have hD : IsClosed D := by
    dsimp only [D]
    simp only [setOf_forall]
    apply isClosed_iInter
    intro e
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const
      (((continuous_normalCoordinate a b).sub continuous_const).abs)
  have hKD : IsCompact (K ∩ D) := hK.inter_right hD
  have hsub : K ∩ D ⊆ regularRegion Ω a b E := by
    intro z hz
    refine ⟨hKΩ hz.1, ?_⟩
    intro he
    have hh := hz.2 (normalCoordinate a b z) he
    simp only [sub_self, abs_zero] at hh
    linarith
  obtain ⟨C, hC, hsec⟩ := exists_cocoercivity_constant_on_smooth_compact
    (isOpen_regularRegion hΩ a b hE) hF hsmooth hKD hsub
  let L : ℝ := ‖gradientFunctional a‖
  have hL : 0 ≤ L := norm_nonneg _
  let ρ : ℝ := δ / (2 * (L + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨C, hC, ρ, hρ, ?_⟩
  intro x hx z hz hτ hstep
  have hnormal : |normalCoordinate a b z - normalCoordinate a b x| < δ / 2 := by
    have he : normalCoordinate a b z - normalCoordinate a b x = gradientFunctional a (z - x) := by
      simp only [normalCoordinate, gradientFunctional_apply]
      change a ⬝ᵥ z - b - (a ⬝ᵥ x - b) = a ⬝ᵥ (z - x)
      rw [dotProduct_sub]
      ring
    rw [he, ← Real.norm_eq_abs]
    calc
      _ ≤ L * ‖z - x‖ := (gradientFunctional a).le_opNorm _
      _ ≤ (L + 1) * ‖z - x‖ := by nlinarith [norm_nonneg (z - x)]
      _ < (L + 1) * ρ := mul_lt_mul_of_pos_left hstep (by positivity)
      _ = δ / 2 := by dsimp [ρ]; field_simp; ring
  have hzfar : ∀ e ∈ E, δ ≤ |normalCoordinate a b z - e| := by
    intro e he
    by_cases hh : δ ≤ |normalCoordinate a b z - e|
    · exact hh
    · exact False.elim (hτ (hzero _ _ he (le_of_lt (lt_of_not_ge hh))))
  have hzD : z ∈ D := by intro e he; linarith [hzfar e he]
  have hxD : x ∈ D := by
    intro e he
    have ht := abs_add (normalCoordinate a b z - normalCoordinate a b x)
      (normalCoordinate a b x - e)
    rw [sub_add_sub_cancel] at ht
    linarith [hzfar e he]
  exact hsec x ⟨hx, hxD⟩ z ⟨hz, hzD⟩

end BfgsVerification.FixedNormal
