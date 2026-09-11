import BfgsVerification.FixedNormalCocoercivity
import BfgsVerification.FixedNormalTangentialStrong

/-! Frame estimates from actual tangential curvature, without full strong
convexity. These lemmas are consumed by the objective-level composite theorem. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
namespace BfgsVerification.AdmissibleBFGSRun
open FixedNormal SmoothSubspace
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem eventually_tangential_frame_secant {r : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (hK : IsCompact R.initialSublevel) (hKΩ : R.initialSublevel ⊆ Ω)
    {a : Vec n} (ha : sqNorm a = 1) (b : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (htan : ∀ k, sqNorm (FixedNormal.tangentProjection a (R.gradientChange k)) ≤ L * R.curvature k)
    (hsteps : Tendsto R.displacement atTop (𝓝 0)) {E : Set ℝ} (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (FixedNormal.regularRegion Ω a b E) F)
    {τ : ℝ → ℝ} (hτb : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ t e, e ∈ E → |t - e| ≤ δ → τ t = 0)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = FixedNormal.tangentProjection a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      sqNorm ((FixedNormal.cutoffFrame U a (τ (FixedNormal.normalCoordinate a b (R.x (k + 1)))))ᵀ.mulVec
        (R.gradientChange k)) ≤ C * R.curvature k := by
  obtain ⟨C, hC, ρ, hρ, hbound⟩ := FixedNormal.exists_cutoff_strip_cocoercivity
    R.convex hΩ hK hKΩ a b hE hsmooth hδ hzero
  refine ⟨L + C, by positivity, ?_⟩
  have hsmall : ∀ᶠ k in atTop, ‖R.displacement k‖ < ρ := by
    have hs := hsteps.norm
    have hs0 : Tendsto (fun k => ‖R.displacement k‖) atTop (𝓝 0) := by simpa using hs
    exact hs0.eventually_lt_const hρ
  filter_upwards [hsmall] with k hk
  have hx (j : ℕ) : R.x j ∈ Ω := hKΩ (R.iterate_mem_initialSublevel j)
  have htcur : 0 ≤ R.curvature k := (R.curvature_pos k).le
  by_cases ht : τ (FixedNormal.normalCoordinate a b (R.x (k + 1))) = 0
  · rw [ht, FixedNormal.cutoffFrame_pairing]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]
    rw [FixedNormal.tangent_matrix_sqNorm a U hU hproj]
    exact (htan k).trans (mul_le_mul_of_nonneg_right (by linarith : L ≤ L + C) htcur)
  · have he : R.x (k + 1) - R.x k = R.displacement k := by rw [R.step]; simp [displacement]
    have hc := hbound _ (R.iterate_mem_initialSublevel k) _
      (R.iterate_mem_initialSublevel (k + 1)) ht (by rwa [he])
    have hcoord (j : ℕ) : coordinateGradient F (R.x j) = R.g j := supporting_vector_eq_gradient
      (convex_supporting_inequality R.convex (hasFDerivAt_coordinateGradient (R.hasGradient j).differentiableAt))
      (R.hasGradient j)
    rw [hcoord, hcoord, he] at hc
    have hs : sqNorm (R.gradientChange k) ≤ C * R.curvature k := hc
    exact (FixedNormal.cutoffFrame_sqNorm_le ha U hU hproj _ (hτb _).1 (hτb _).2).trans
      (hs.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ L + C) htcur))

/-- U.15 uses only projected displacement curvature; its full-curvature
strengthening is unnecessary for the composite class. -/
theorem tangential_cutoff_residual_budget {r : ℕ} {Ω : Set (Vec n)}
    {a : Vec n} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ConvexOn ℝ Ω (fun x => F x - (μ / 2) * sqNorm (tangentProjection a x)))
    (hx : ∀ k, R.x k ∈ Ω) {τ : ℝ → ℝ} {L : ℝ≥0}
    (hτ : LipschitzWith L τ) (b : ℝ) (k : ℕ) :
    frobSq (cutoffResidual (r := r) a (R.displacement k)
      (cutoffSlope τ (normalCoordinate a b (R.x k)) (normalCoordinate a b (R.x (k + 1))))) ≤
        (2 * (L : ℝ) ^ 2 / μ) * R.d k := by
  rw [cutoffResidual_frobSq]
  have hβ := abs_cutoffSlope_le hτ (normalCoordinate a b (R.x k))
    (normalCoordinate a b (R.x (k + 1)))
  have hβsq : (cutoffSlope τ (normalCoordinate a b (R.x k))
      (normalCoordinate a b (R.x (k + 1)))) ^ 2 ≤ (L : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr hβ
  have hd := R.projected_displacement_sq_le (tangentMap a) hμ hstrong hx k
  calc
    _ ≤ (L : ℝ) ^ 2 * sqNorm (tangentProjection a (R.displacement k)) :=
      mul_le_mul_of_nonneg_right hβsq (sqNorm_nonneg _)
    _ ≤ (L : ℝ) ^ 2 * ((2 / μ) * R.d k) := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = _ := by ring

end BfgsVerification.AdmissibleBFGSRun
