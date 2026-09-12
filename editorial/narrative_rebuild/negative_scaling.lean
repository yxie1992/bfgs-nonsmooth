import BfgsVerification.BFGSGradientScaling

/-! Mathematical covariance of the actual full inverse-BFGS formulas.
This file does not assert existence of an orbit or containment of any query.
The D and L construction contracts supply those separate facts. -/

noncomputable section
namespace NarrativeNegativeScaling
open BfgsVerification

private theorem scale_product {spatial objective : ℝ}
    (hl : spatial ≠ 0) (hs : objective ≠ 0) :
    (spatial ^ 2 / objective) * (objective / spatial) = spatial := by
  field_simp
  ring

theorem step_covariance {n : ℕ} (H : Mat n) (g : Vec n) (a : ℝ)
    {spatial objective : ℝ} (hl : spatial ≠ 0) (hs : objective ≠ 0) :
    bfgsStep ((spatial ^ 2 / objective) • H) ((objective / spatial) • g) a =
      spatial • bfgsStep H g a := by
  rw [bfgsStep_scale_gradient, bfgsStep_scale_matrix, smul_smul,
    mul_comm (objective / spatial), scale_product hl hs]

theorem inverse_update_covariance {n : ℕ} (H : Mat n) (s y : Vec n)
    {spatial objective : ℝ} (hl : spatial ≠ 0) (hs : objective ≠ 0) :
    inverseBFGS ((spatial ^ 2 / objective) • H) (spatial • s)
      ((objective / spatial) • y) =
      (spatial ^ 2 / objective) • inverseBFGS H s y := by
  have hq : spatial ^ 2 / objective ≠ 0 := div_ne_zero (pow_ne_zero 2 hl) hs
  have ht : objective / spatial ≠ 0 := div_ne_zero hs hl
  have heq : spatial • s =
      (objective / spatial) • ((spatial ^ 2 / objective) • s) := by
    rw [smul_smul, mul_comm (objective / spatial), scale_product hl hs]
  rw [heq, inverseBFGS_scale_secant_pair _ _ _ ht, inverseBFGS_scale _ _ _ hq]

theorem pairing_covariance {n : ℕ} (g s : Vec n)
    {spatial objective : ℝ} (hl : spatial ≠ 0) :
    dot ((objective / spatial) • g) (spatial • s) = objective * dot g s := by
  rw [dot_smul_right, PlanarUpdate.dot_scale_left]
  field_simp

theorem objective_difference (C objective u v : ℝ) :
    (C + objective * u) - (C + objective * v) = objective * (u - v) := by
  ring

theorem scaled_comparison {objective : ℝ} (hs : 0 < objective) (C u v : ℝ) :
    (C + objective * u ≤ C + objective * v ↔ u ≤ v) ∧
    (C + objective * u < C + objective * v ↔ u < v) := by
  constructor <;> simp only [add_le_add_iff_left, add_lt_add_iff_left,
    mul_le_mul_left hs, mul_lt_mul_left hs]

theorem armijo_comparison {n : ℕ} (g p : Vec n) (C f fTrial c a : ℝ)
    {spatial objective : ℝ} (hl : spatial ≠ 0) (hs : 0 < objective) :
    (C + objective * fTrial ≤ C + objective * f +
        c * a * dot ((objective / spatial) • g) (spatial • p) ↔
      fTrial ≤ f + c * a * dot g p) ∧
    (C + objective * fTrial < C + objective * f +
        c * a * dot ((objective / spatial) • g) (spatial • p) ↔
      fTrial < f + c * a * dot g p) := by
  rw [pairing_covariance _ _ hl]
  have h : C + objective * f + c * a * (objective * dot g p) =
      C + objective * (f + c * a * dot g p) := by ring
  rw [h]
  exact scaled_comparison hs C _ _

theorem wolfe_comparison {n : ℕ} (g gTrial p : Vec n) (c : ℝ)
    {spatial objective : ℝ} (hl : spatial ≠ 0) (hs : 0 < objective) :
    (c * dot ((objective / spatial) • g) (spatial • p) ≤
        dot ((objective / spatial) • gTrial) (spatial • p) ↔
      c * dot g p ≤ dot gTrial p) ∧
    (c * dot ((objective / spatial) • g) (spatial • p) <
        dot ((objective / spatial) • gTrial) (spatial • p) ↔
      c * dot g p < dot gTrial p) := by
  rw [pairing_covariance _ _ hl, pairing_covariance _ _ hl]
  have h : c * (objective * dot g p) = objective * (c * dot g p) := by ring
  rw [h]
  constructor
  · exact mul_le_mul_left hs
  · exact mul_lt_mul_left hs

theorem matched_scale_preserves_matrix {n : ℕ} (H : Mat n)
    {spatial : ℝ} (hl : spatial ≠ 0) : (spatial ^ 2 / spatial ^ 2) • H = H := by
  rw [div_self (pow_ne_zero 2 hl), one_smul]

end NarrativeNegativeScaling
