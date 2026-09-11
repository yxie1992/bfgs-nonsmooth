import BfgsVerification.PlanarBFGSUpdate
noncomputable section
open Matrix
namespace BfgsVerification

theorem outer_scale_left {n : ℕ} (r : ℝ) (u v : Vec n) : outer (r • u) v=r • outer u v := by
  ext i j
  simp only [outer,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem outer_scale_right {n : ℕ} (r : ℝ) (u v : Vec n) : outer u (r • v)=r • outer u v := by
  ext i j
  simp only [outer,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem bfgsStep_scale_matrix {n : ℕ} (r a : ℝ) (H : Mat n) (g : Vec n) :
    bfgsStep (r • H) g a=r • bfgsStep H g a := by
  simp only [bfgsStep,Matrix.smul_mulVec_assoc]
  exact smul_comm _ _ _

theorem inverseBFGS_scale {n : ℕ} (H : Mat n) (s y : Vec n) {r : ℝ} (hr : r ≠ 0) :
    inverseBFGS (r • H) (r • s) y=r • inverseBFGS H s y := by
  have hscalar (t : ℝ) : (r*t)⁻¹*r=t⁻¹ := by
    rw [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ hr,mul_one]
  have hleft : (dot y (r • s))⁻¹ • outer (r • s) y=(dot y s)⁻¹ • outer s y := by
    rw [dot_smul_right,outer_scale_left,smul_smul,hscalar]
  have hright : (dot y (r • s))⁻¹ • outer y (r • s)=(dot y s)⁻¹ • outer y s := by
    rw [dot_smul_right,outer_scale_right,smul_smul,hscalar]
  have houter : (dot y (r • s))⁻¹ • outer (r • s) (r • s)=r • ((dot y s)⁻¹ • outer s s) := by
    rw [dot_smul_right,outer_scale_left,outer_scale_right,smul_smul,hscalar]
    rw [smul_comm]
  simp only [inverseBFGS,hleft,hright,houter,Matrix.mul_smul,Matrix.smul_mul,smul_add]

end BfgsVerification
