import BfgsVerification.TwoPieceRay
import BfgsVerification.AffineImageRun

noncomputable section
open scoped BigOperators
open Set Matrix
namespace BfgsVerification.TwoPieceBudget

theorem fullRowRank_of_row_independence {n r : ℕ}
    (Q : Matrix (Fin r) (Fin n) ℝ) (hQ : LinearIndependent ℝ Q) :
    AffineProjection.FullRowRank Q := by
  intro x y hxy
  have hz : Qᵀ.mulVec (x-y)=0 := by rw [Matrix.mulVec_sub,hxy,sub_self]
  have he : ∑ i, (x-y) i • Q i=0 := by
    ext j
    have hh := congrArg (fun v : Vec n => v j) hz
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul,mul_comm,Pi.zero_apply] using hh
  have hcoef := (Fintype.linearIndependent_iff.mp hQ) (x-y) he
  ext i
  exact sub_eq_zero.mp (hcoef i)

def rowMatrix {n : ℕ} (u v : Vec n) : Matrix (Fin 2) (Fin n) ℝ := ![u,v]

theorem image_objective {n : ℕ} (u v x : Vec n) :
    objective ((rowMatrix u v).mulVec x)=|dot u x|+dot v x := by
  simp [objective,rowMatrix,Matrix.mulVec,dotProduct,dot]

/-- Actual arbitrary-dimensional full-BFGS projection, with no discarded
off-plane metric entries or assumed matrix behavior. -/
theorem no_infinite_linear_image {n : ℕ} (Q : Matrix (Fin 2) (Fin n) ℝ)
    (hQ : AffineProjection.FullRowRank Q)
    (R : AdmissibleBFGSRun n (fun x => objective (Q.mulVec x))) : False :=
  no_infinite_actual_run (AffineProjection.projectRun Q hQ objective R)

theorem no_infinite_independent_two_piece {n : ℕ} (u v : Vec n)
    (h : LinearIndependent ℝ ![u,v])
    (R : AdmissibleBFGSRun n (fun x => |dot u x|+dot v x)) : False := by
  have he : (fun x => |dot u x|+dot v x) = (fun x => objective ((rowMatrix u v).mulVec x)) :=
    funext (fun x => (image_objective u v x).symm)
  rw [he] at R
  exact no_infinite_linear_image (rowMatrix u v) (fullRowRank_of_row_independence _ h) R

end BfgsVerification.TwoPieceBudget
