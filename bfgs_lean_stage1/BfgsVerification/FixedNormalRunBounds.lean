import BfgsVerification.FixedNormalFrame

/-! Objective-derived tangential secant, actual Hessian trace, and cutoff
residual budgets for Module U. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix

namespace BfgsVerification
namespace FixedNormal

/-- Explicit compatibility of the actual Euclidean square and the finite-Pi
norm; the dimension factor is used only to convert a Lipschitz constant. -/
theorem sqNorm_le_dim_mul_norm_sq {n : ℕ} (v : Vec n) :
    sqNorm v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  calc
    sqNorm v ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (norm_nonneg (v i)) (norm_nonneg v)).mpr (norm_le_pi_norm v i)
      simpa only [Real.norm_eq_abs, sq_abs] using h
    _ = (n : ℝ) * ‖v‖ ^ 2 := by simp

/-- A standard ambient Lipschitz field has an explicit Euclidean square bound. -/
theorem lipschitz_sqNorm_bound {n : ℕ} {A : Vec n → Vec n} {L : ℝ≥0}
    {U : Set (Vec n)} (hA : LipschitzOnWith L A U) {x z : Vec n}
    (hx : x ∈ U) (hz : z ∈ U) :
    sqNorm (A z - A x) ≤ ((n : ℝ) * (L : ℝ) ^ 2) * sqNorm (z - x) := by
  calc
    sqNorm (A z - A x) ≤ (n : ℝ) * ‖A z - A x‖ ^ 2 := sqNorm_le_dim_mul_norm_sq _
    _ ≤ (n : ℝ) * ((L : ℝ) * ‖z - x‖) ^ 2 := by
      gcongr
      exact hA.norm_sub_le hz hx
    _ ≤ ((n : ℝ) * (L : ℝ) ^ 2) * sqNorm (z - x) := by
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (CenteredSmoothSublinear.pi_norm_sq_le_sqNorm _)
        (by positivity)

end FixedNormal

namespace AdmissibleBFGSRun
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The common projection premise is about all actual subgradients of the
objective, and gives the actual accepted-gradient secant identity. -/
theorem tangent_gradientChange {Ω : Set (Vec n)} {a : Vec n} {A : Vec n → Vec n}
    (hx : ∀ k, R.x k ∈ Ω)
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → FixedNormal.tangentProjection a g = A x)
    (k : ℕ) :
    FixedNormal.tangentProjection a (R.gradientChange k) = A (R.x (k + 1)) - A (R.x k) := by
  change FixedNormal.tangentMap a (R.g (k + 1) - R.g k) = _
  rw [map_sub, FixedNormal.tangentMap_apply, FixedNormal.tangentMap_apply,
    hA _ (hx (k + 1)) _ (convex_supporting_inequality R.convex (R.hasGradient (k + 1))),
    hA _ (hx k) _ (convex_supporting_inequality R.convex (R.hasGradient k))]

/-- U.11 derives a uniform smooth-subspace secant constant from objective
strong convexity and the actual Lipschitz tangential field. -/
theorem fixed_normal_tangent_secant {r : ℕ} {Ω : Set (Vec n)} {a : Vec n}
    {A : Vec n → Vec n} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : FixedNormal.EuclideanStrongConvexOn Ω μ F)
    (hx : ∀ k, R.x k ∈ Ω)
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → FixedNormal.tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = FixedNormal.tangentProjection a v) (k : ℕ) :
    sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤
      ((n : ℝ) * (L : ℝ) ^ 2 / μ) * R.curvature k := by
  rw [FixedNormal.tangent_matrix_sqNorm a U hU hproj, R.tangent_gradientChange hx hA]
  have hl := FixedNormal.lipschitz_sqNorm_bound hLip (hx k) (hx (k + 1))
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [displacement]
  rw [he] at hl
  have hs : sqNorm (R.displacement k) ≤ R.curvature k / μ :=
    (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using R.strong_curvature_bound hstrong hx k)
  exact hl.trans (by
    convert mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (n : ℝ) * (L : ℝ) ^ 2) using 1 <;> ring)

/-- The claimed controlled tangent Hessian growth is derived for the actual
full-BFGS matrices from objective regularity. -/
theorem fixed_normal_hessian_trace_budget {r : ℕ} {Ω : Set (Vec n)} {a : Vec n}
    {A : Vec n → Vec n} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : FixedNormal.EuclideanStrongConvexOn Ω μ F)
    (hx : ∀ k, R.x k ∈ Ω)
    (hA : ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → FixedNormal.tangentProjection a g = A x)
    {L : ℝ≥0} (hLip : LipschitzOnWith L A Ω)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hproj : ∀ v, (U * Uᵀ).mulVec v = FixedNormal.tangentProjection a v) (k : ℕ) :
    (metricGram (R.hessian k) U).trace ≤ (metricGram (R.hessian 0) U).trace +
      ((n : ℝ) * (L : ℝ) ^ 2 / μ) * (k : ℝ) :=
  R.smooth_subspace_trace_bound U _ (R.fixed_normal_tangent_secant hμ hstrong hx hA hLip U hU hproj) k

/-- U.15 derives the actual cutoff residual budget in predicted-decrease units. -/
theorem fixed_normal_cutoff_residual_budget {r : ℕ} {Ω : Set (Vec n)} {μ : ℝ}
    (hμ : 0 < μ) (hstrong : FixedNormal.EuclideanStrongConvexOn Ω μ F)
    (hx : ∀ k, R.x k ∈ Ω) {a : Vec n} (ha : sqNorm a = 1)
    {τ : ℝ → ℝ} {L : ℝ≥0} (hτ : LipschitzWith L τ) (b : ℝ) (k : ℕ) :
    SmoothSubspace.frobSq (FixedNormal.cutoffResidual (r := r) a (R.displacement k)
      (FixedNormal.cutoffSlope τ (dot a (R.x k) - b) (dot a (R.x (k + 1)) - b))) ≤
      (2 * (L : ℝ) ^ 2 / μ) * R.d k := by
  have hb := FixedNormal.cutoffResidual_bound (r := r) ha hτ (R.x k) (R.x (k + 1)) b
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [displacement]
  rw [he] at hb
  calc
    _ ≤ (L : ℝ) ^ 2 * sqNorm (R.displacement k) := hb
    _ ≤ (L : ℝ) ^ 2 * ((2 / μ) * R.d k) :=
      mul_le_mul_of_nonneg_left (R.strong_displacement_sq_le hμ hstrong hx k) (sq_nonneg _)
    _ = _ := by ring

end AdmissibleBFGSRun
end BfgsVerification
