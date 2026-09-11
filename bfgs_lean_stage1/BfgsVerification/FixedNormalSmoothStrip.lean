import BfgsVerification.FixedNormalVisibility

/-! Uniform accepted secant estimates away from the exceptional scalar levels.
For the strongly convex U.1/U.2 cases, local gradient Lipschitz continuity and
the already derived strong curvature bound suffice; no global C1,1 is assumed. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace FixedNormal

theorem sqNorm_coordinateGradient_sub_le {n : ℕ} (F : Vec n → ℝ) (x z : Vec n) :
    sqNorm (coordinateGradient F z - coordinateGradient F x) ≤
      (n : ℝ) * ‖fderiv ℝ F z - fderiv ℝ F x‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin n, ‖fderiv ℝ F z - fderiv ℝ F x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hn := (fderiv ℝ F z - fderiv ℝ F x).le_opNorm (Pi.single i (1 : ℝ))
      simp only [Pi.norm_single, norm_one, mul_one] at hn
      have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
      simpa only [coordinateGradient, Pi.sub_apply, ContinuousLinearMap.sub_apply,
        Real.norm_eq_abs, sq_abs] using hs
    _ = _ := by simp

/-- Compactness of the part a positive fixed distance from every exceptional
level yields one full-ball derivative Lipschitz bound. The exceptional set may
be empty or infinite. -/
theorem exists_smooth_strip_secant_bound {n : ℕ} {F : Vec n → ℝ}
    {Ω K : Set (Vec n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ K, ∀ z ∈ K, τ (normalCoordinate a b z) ≠ 0 → ‖z - x‖ < ρ →
        sqNorm (coordinateGradient F z - coordinateGradient F x) ≤ C * sqNorm (z - x) := by
  let D : Set (Vec n) := {z | ∀ e ∈ E, δ ≤ |normalCoordinate a b z - e|}
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
  obtain ⟨M, ρ, hρ, hballs⟩ := CenteredSmoothSublinear.compact_uniform_local_lipschitz
    (isOpen_regularRegion hΩ a b hE) hKD hsub hsmooth.2
  refine ⟨(n : ℝ) * (M : ℝ) ^ 2, by positivity, ρ, hρ, ?_⟩
  intro x hx z hz hτ hxz
  have hzD : z ∈ D := by
    intro e he
    by_contra hn
    exact hτ (hzero _ _ he (le_of_lt (lt_of_not_ge hn)))
  have hxball : x ∈ ball z ρ := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hxz
  have hfd := (hballs z ⟨hz, hzD⟩).2.norm_sub_le (mem_ball_self hρ) hxball
  calc
    _ ≤ (n : ℝ) * ‖fderiv ℝ F z - fderiv ℝ F x‖ ^ 2 := sqNorm_coordinateGradient_sub_le F x z
    _ ≤ (n : ℝ) * ((M : ℝ) * ‖z - x‖) ^ 2 := by
      gcongr
    _ ≤ ((n : ℝ) * (M : ℝ) ^ 2) * sqNorm (z - x) := by
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (CenteredSmoothSublinear.pi_norm_sq_le_sqNorm _) (by positivity)

/-- A cutoff between zero and one only contracts the normal coordinate. -/
theorem cutoffFrame_sqNorm_le {n r : ℕ} {a : Vec n} (ha : sqNorm a = 1)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = tangentProjection a v)
    (y : Vec n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sqNorm ((cutoffFrame U a t)ᵀ.mulVec y) ≤ sqNorm y := by
  rw [cutoffFrame_pairing, tangent_matrix_sqNorm a U hU hproj]
  have ht : t ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg (dot a y))
  have hpy := tangentProjection_pythagorean ha y
  nlinarith

end FixedNormal

namespace AdmissibleBFGSRun
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- U.13 for the entire actual late trajectory. All smooth-strip constants and
the small-step tail are derived from objective assumptions. -/
theorem eventually_fixed_normal_frame_secant {r : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : FixedNormal.EuclideanStrongConvexOn Ω μ F)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {A : Vec n → Vec n}
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → FixedNormal.tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (FixedNormal.regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} (hτb : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = FixedNormal.tangentProjection a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      sqNorm ((FixedNormal.cutoffFrame U a (τ (FixedNormal.normalCoordinate a b (R.x (k + 1)))))ᵀ.mulVec
        (R.gradientChange k)) ≤ C * R.curvature k := by
  obtain ⟨C, hC, ρ, hρ, hbound⟩ := FixedNormal.exists_smooth_strip_secant_bound
    hΩ hK hKΩ a b hE hsmooth hδ hzero
  let T : ℝ := (n : ℝ) * (L : ℝ) ^ 2 / μ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨T + C / μ, by positivity, ?_⟩
  have hsteps : ∀ᶠ k in atTop, ‖R.displacement k‖ < ρ := by
    have hs := (R.displacement_tendsto_zero_of_strong_convexity hμ hstrong hK hKΩ).norm
    have hs0 : Tendsto (fun k => ‖R.displacement k‖) atTop (𝓝 0) := by simpa using hs
    exact hs0.eventually_lt_const hρ
  filter_upwards [hsteps] with k hk
  have hx (j : ℕ) : R.x j ∈ Ω := hKΩ (R.iterate_mem_initialSublevel j)
  have htcur : 0 ≤ R.curvature k := (R.curvature_pos k).le
  by_cases ht : τ (FixedNormal.normalCoordinate a b (R.x (k + 1))) = 0
  · rw [ht, FixedNormal.cutoffFrame_pairing]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]
    exact (R.fixed_normal_tangent_secant hμ hstrong hx hA hLip U hU hproj k).trans
      (mul_le_mul_of_nonneg_right (by linarith [div_nonneg hC hμ.le] : T ≤ T + C / μ) htcur)
  · have he : R.x (k + 1) - R.x k = R.displacement k := by rw [R.step]; simp [displacement]
    have hc := hbound _ (R.iterate_mem_initialSublevel k) _
      (R.iterate_mem_initialSublevel (k + 1)) ht (by rwa [he])
    have hcoord (j : ℕ) : coordinateGradient F (R.x j) = R.g j := supporting_vector_eq_gradient
      (convex_supporting_inequality R.convex (hasFDerivAt_coordinateGradient (R.hasGradient j).differentiableAt))
      (R.hasGradient j)
    rw [hcoord, hcoord, he] at hc
    have hcur : sqNorm (R.displacement k) ≤ R.curvature k / μ :=
      (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using R.strong_curvature_bound hstrong hx k)
    have hs : sqNorm (R.gradientChange k) ≤ (C / μ) * R.curvature k := hc.trans (by
      convert mul_le_mul_of_nonneg_left hcur hC using 1 <;> ring)
    exact (FixedNormal.cutoffFrame_sqNorm_le ha U hU hproj _ (hτb _).1 (hτb _).2).trans
      (hs.trans (mul_le_mul_of_nonneg_right (by linarith : C / μ ≤ T + C / μ) htcur))

end AdmissibleBFGSRun
end BfgsVerification
