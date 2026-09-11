import BfgsVerification.BFGSCompression
import BfgsVerification.PositiveUpdate
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.PlanarUpdate

def perp (y : Vec 2) : Vec 2 := ![-y 1,y 0]

theorem dot_scale_left {n : ℕ} (r : ℝ) (x y : Vec n) : dot (r • x) y = r*dot x y := by
  simp only [dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem projector_formula (s y : Vec 2) (ht : dot y s ≠ 0) :
    1-(dot y s)⁻¹ • outer s y = (dot y s)⁻¹ • outer (perp y) (perp s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [outer,perp]
  all_goals field_simp [ht]
  all_goals norm_num [dot,Fin.sum_univ_two]; ring

theorem inverse_formula (H : Mat 2) (s y : Vec 2) (ht : dot y s ≠ 0) :
    inverseBFGS H s y =
      (dot (perp s) (H.mulVec (perp s))/(dot y s)^2) • outer (perp y) (perp y) +
        (dot y s)⁻¹ • outer s s := by
  have hcomm : dot s y=dot y s := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht' : dot s y ≠ 0 := by rwa [hcomm]
  have hp := projector_formula s y ht
  have hp' := projector_formula y s ht'
  rw [hcomm] at hp'
  simp only [inverseBFGS,hp,hp']
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [outer,perp,dot,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  all_goals simp only [dot,Fin.sum_univ_two] at ht
  all_goals field_simp [ht]
  all_goals ring

theorem aligned_identity (H : Mat 2) (y : Vec 2) {ρ : ℝ}
    (hρ : ρ ≠ 0) (hy : dot y y ≠ 0)
    (henergy : dot (perp y) (H.mulVec (perp y)) = ρ*dot y y) :
    inverseBFGS H (ρ • y) y = ρ • (1 : Mat 2) := by
  have ht : dot y (ρ • y) ≠ 0 := by rw [dot_smul_right]; exact mul_ne_zero hρ hy
  rw [inverse_formula H (ρ • y) y ht]
  have hp : perp (ρ • y)=ρ • perp y := by ext i; fin_cases i <;> simp [perp]
  rw [hp,Matrix.mulVec_smul,dot_scale_left,dot_smul_right,henergy,dot_smul_right]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [outer,perp]
  all_goals field_simp [hρ,hy]
  all_goals norm_num [dot,Fin.sum_univ_two]; ring

end BfgsVerification.PlanarUpdate
