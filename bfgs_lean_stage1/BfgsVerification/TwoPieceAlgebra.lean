import BfgsVerification.PlanarBFGSUpdate
import BfgsVerification.TwoPieceScalarBudget

set_option maxHeartbeats 2000000
noncomputable section
open Matrix
namespace BfgsVerification.TwoPieceBudget

def matrix (a b c : ℝ) : Mat 2 := ![![a,b],![b,c]]
def gradient (σ : ℝ) : Vec 2 := ![σ,1]
def energy (a b c σ : ℝ) : ℝ := a+2*σ*b+c
def cross (a b σ : ℝ) : ℝ := a+σ*b
def determinant (a b c : ℝ) : ℝ := a*c-b^2

theorem step_formula (a b c σ α : ℝ) (hσ : σ^2=1) :
    bfgsStep (matrix a b c) (gradient σ) α =
      ![-α*σ*cross a b σ,-α*(energy a b c σ-cross a b σ)] := by
  obtain rfl | rfl := sq_eq_one_iff.mp hσ
  all_goals
    ext i
    fin_cases i <;>
      simp [bfgsStep,matrix,gradient,cross,energy,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring_nf <;> simp

theorem gradient_change (σ : ℝ) : gradient (-σ)-gradient σ = ![-2*σ,0] := by
  ext i
  fin_cases i <;> simp [gradient] <;> ring

theorem curvature_formula (a b c σ α : ℝ) (hσ : σ^2=1) :
    dot (gradient (-σ)-gradient σ) (bfgsStep (matrix a b c) (gradient σ) α) =
      2*α*cross a b σ := by
  rw [step_formula a b c σ α hσ,gradient_change]
  simp only [dot,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ = 2*α*cross a b σ*σ^2 := by ring
    _ = _ := by rw [hσ]; ring

theorem actual_update_matrix (a b c σ α : ℝ) (hσ : σ^2=1)
    (hα : α ≠ 0) (hB : cross a b σ ≠ 0) :
    inverseBFGS (matrix a b c) (bfgsStep (matrix a b c) (gradient σ) α)
      (gradient (-σ)-gradient σ) =
    matrix (α*cross a b σ/2)
      (σ*α*(energy a b c σ-cross a b σ)/2)
      (determinant a b c*energy a b c σ/(cross a b σ)^2 +
        α*(energy a b c σ-cross a b σ)^2/(2*cross a b σ)) := by
  have ht : dot (gradient (-σ)-gradient σ)
      (bfgsStep (matrix a b c) (gradient σ) α) ≠ 0 := by
    rw [curvature_formula a b c σ α hσ]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hα) hB
  rw [PlanarUpdate.inverse_formula _ _ _ ht,curvature_formula a b c σ α hσ,step_formula a b c σ α hσ,gradient_change]
  obtain rfl | rfl := sq_eq_one_iff.mp hσ
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix,PlanarUpdate.perp,outer,dot,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    all_goals
      dsimp [cross,energy,determinant] at *
      simp only [one_mul,neg_one_mul] at *
      field_simp [hB,hα]
      <;> ring

theorem scalar_update_identities (a b c σ α : ℝ) (hσ : σ^2=1)
    (hB : cross a b σ ≠ 0) :
    let A := energy a b c σ
    let B := cross a b σ
    let D := determinant a b c
    let a' := α*B/2
    let b' := σ*α*(A-B)/2
    let c' := D*A/B^2+α*(A-B)^2/(2*B)
    energy a' b' c' (-σ)=D*A/B^2+α*(A-2*B)^2/(2*B) ∧
    cross a' b' (-σ)=α*(B-A/2) ∧
    determinant a' b' c'=α*A*D/(2*B) := by
  dsimp only
  obtain rfl | rfl := sq_eq_one_iff.mp hσ
  all_goals
    dsimp [energy,cross,determinant] at *
    simp only [one_mul,neg_one_mul] at *
    constructor
    · field_simp [hB]; ring
    · constructor
      · ring
      · field_simp [hB]; ring

end BfgsVerification.TwoPieceBudget
