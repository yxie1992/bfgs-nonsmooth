import BfgsVerification.BFGSScaling

/-! Simultaneous secant-pair scaling for the actual full inverse-BFGS update. -/

noncomputable section
open Matrix
namespace BfgsVerification

theorem bfgsStep_scale_gradient {n : ℕ} (r a : ℝ) (H : Mat n) (g : Vec n) :
    bfgsStep H (r • g) a = r • bfgsStep H g a := by
  simp only [bfgsStep, Matrix.mulVec_smul]
  exact smul_comm _ _ _

theorem inverseBFGS_scale_secant_pair {n : ℕ} (H : Mat n) (s y : Vec n)
    {r : ℝ} (hr : r ≠ 0) :
    inverseBFGS H (r • s) (r • y) = inverseBFGS H s y := by
  have hd : dot (r • y) (r • s) = r * r * dot y s := by
    rw [dot_smul_right, PlanarUpdate.dot_scale_left]
    ring
  have hc (t : ℝ) : (r * r * t)⁻¹ * (r * r) = t⁻¹ := by
    rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr hr), mul_one]
  have ho (u v : Vec n) :
      (dot (r • y) (r • s))⁻¹ • outer (r • u) (r • v) =
        (dot y s)⁻¹ • outer u v := by
    rw [hd, outer_scale_left, outer_scale_right, smul_smul, smul_smul]
    rw [mul_assoc _ r r, hc]
  simp only [inverseBFGS, ho]

end BfgsVerification
