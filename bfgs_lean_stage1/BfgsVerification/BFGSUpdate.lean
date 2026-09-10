import BfgsVerification.Definitions

/-! Exact algebra of the unmodified full inverse-BFGS update. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification

theorem dot_smul_right {n : ℕ} (a : ℝ) (x y : Vec n) :
    dot x (a • y) = a * dot x y := by
  unfold dot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem curvature_eq_alpha_beta_q {n : ℕ} (H : Mat n) (g y : Vec n) (α : ℝ)
    (hq : metricEnergy H g ≠ 0) :
    dot y (bfgsStep H g α) =
      α * (-dot y (H.mulVec g) / metricEnergy H g) * metricEnergy H g := by
  rw [bfgsStep, dot_smul_right]
  field_simp
  <;> ring

/-- The ordinary full inverse-BFGS formula equals the projected matrix plus
its rank-one increment. No matrix convergence or spectral bound is used. -/
theorem inverseBFGS_projection_form {n : ℕ} (H : Mat n) (g y : Vec n) (α : ℝ)
    (hα : α ≠ 0) (hq : metricEnergy H g ≠ 0)
    (hb : -dot y (H.mulVec g) / metricEnergy H g ≠ 0) :
    let q := metricEnergy H g
    let β := -dot y (H.mulVec g) / q
    let v := H.mulVec g
    inverseBFGS H (bfgsStep H g α) y =
      (1 + (β * q)⁻¹ • outer v y) * H *
        (1 + (β * q)⁻¹ • outer y v) +
      (α / (β * q)) • outer v v := by
  dsimp only
  let q := metricEnergy H g
  let β := -dot y (H.mulVec g) / q
  let v := H.mulVec g
  change inverseBFGS H (bfgsStep H g α) y =
    (1 + (β * q)⁻¹ • outer v y) * H *
      (1 + (β * q)⁻¹ • outer y v) + (α / (β * q)) • outer v v
  have ht : dot y (bfgsStep H g α) = α * β * q :=
    curvature_eq_alpha_beta_q H g y α hq
  have hβ : β ≠ 0 := hb
  have hq' : q ≠ 0 := hq
  have hleft : 1 - (α * β * q)⁻¹ • outer (bfgsStep H g α) y =
      (1 : Mat n) + (β * q)⁻¹ • outer v y := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, outer, bfgsStep, Pi.smul_apply]
    dsimp only [v]
    field_simp
    <;> ring
  have hright : 1 - (α * β * q)⁻¹ • outer y (bfgsStep H g α) =
      (1 : Mat n) + (β * q)⁻¹ • outer y v := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, outer, bfgsStep, Pi.smul_apply]
    dsimp only [v]
    field_simp
    <;> ring
  have hrank : (α * β * q)⁻¹ • outer (bfgsStep H g α) (bfgsStep H g α) =
      (α / (β * q)) • outer v v := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, outer, bfgsStep, Pi.smul_apply]
    dsimp only [v]
    field_simp
    <;> ring
  unfold inverseBFGS
  rw [ht]
  dsimp only
  rw [hleft, hright, hrank]

theorem dot_sub_left {n : ℕ} (x y z : Vec n) :
    dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The predicted decrease is exactly minus the accepted directional product. -/
theorem FullBFGSRun.d_eq_neg_dot_step {n : ℕ} (R : FullBFGSRun n) (k : ℕ) :
    R.d k = -dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) := by
  rw [bfgsStep, dot_smul_right]
  unfold FullBFGSRun.d FullBFGSRun.q metricEnergy
  ring

/-- The curvature scalar in the matrix theorem is the ordinary weak-Wolfe
curvature divided by the predicted decrease. -/
theorem FullBFGSRun.curvature_eq_beta_mul_d {n : ℕ} (R : FullBFGSRun n) (k : ℕ) :
    dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) =
      R.beta k * R.d k := by
  rw [curvature_eq_alpha_beta_q _ _ _ _ (ne_of_gt (R.energy_pos k))]
  unfold FullBFGSRun.beta FullBFGSRun.d FullBFGSRun.q
  ring

/-- The lower bound used by the normalization is derived directly from the
weak-Wolfe accepted-step inequality, with no strong-Wolfe assumption. -/
theorem FullBFGSRun.beta_ge_of_weakWolfe {n : ℕ} (R : FullBFGSRun n)
    (k : ℕ) (c₂ : ℝ)
    (hw : c₂ * dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ≤
      dot (R.g (k + 1)) (bfgsStep (R.H k) (R.g k) (R.α k))) :
    1 - c₂ ≤ R.beta k := by
  have hd : 0 < R.d k := mul_pos (R.alpha_pos k) (R.energy_pos k)
  have hcurv := R.curvature_eq_beta_mul_d k
  rw [dot_sub_left] at hcurv
  have hdir := R.d_eq_neg_dot_step k
  have hdir' : dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) = -R.d k := by
    linarith
  rw [hdir'] at hw hcurv
  apply (mul_le_mul_right hd).mp
  nlinarith

end BfgsVerification
