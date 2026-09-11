import BfgsVerification.QuadraticGaugeConvex
import BfgsVerification.PairRealizability
import BfgsVerification.RadialCertificate

/-! Module C's literal three-dimensional smooth quadratic and canonical field. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace SpatialQuadraticWarning

def Q : Mat 3 := diagonal ![1,2,3]
def objective (x : Vec 3) : ℝ := metricEnergy Q x / 2
def gradient (x : Vec 3) : Vec 3 := Q.mulVec x
def base : Vec 3 := ![1,1,1]
def step (ε : ℝ) : Vec 3 := ![ε,0,-(ε+ε^2)/3]
def next (ε : ℝ) : Vec 3 := base + step ε
def change (ε : ℝ) : Vec 3 := gradient (next ε)-gradient base
def canonicalField (x : Vec 3) : Vec 3 := (sqNorm (gradient x))⁻¹ • gradient x

theorem Q_posDef : Q.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

theorem gradient_coordinates (x : Vec 3) : gradient x = ![x 0,2*x 1,3*x 2] := by
  ext i
  fin_cases i <;> simp [gradient,Q,Matrix.mulVec_diagonal]

theorem objective_coordinates (x : Vec 3) :
    objective x = ((x 0)^2+2*(x 1)^2+3*(x 2)^2)/2 := by
  simp [objective,metricEnergy,Q,Matrix.mulVec_diagonal,dot,Fin.sum_univ_succ]
  ring

theorem objective_hasGradient (x : Vec 3) :
    HasFDerivAt objective (gradientFunctional (gradient x)) x :=
  QuadraticGauge.quadratic_hasGradient Q (Matrix.isSymm_diagonal _) x

theorem objective_contDiff {N : WithTop ℕ∞} : ContDiff ℝ N objective := by
  have he : objective = fun x : Vec 3 => ((x 0)^2+2*(x 1)^2+3*(x 2)^2)/2 :=
    funext objective_coordinates
  rw [he]
  fun_prop (disch := norm_num)

theorem objective_convex : ConvexOn ℝ univ objective :=
  QuadraticGauge.quadratic_convex Q Q_posDef.posSemidef

theorem gradient_contDiff {N : WithTop ℕ∞} : ContDiff ℝ N gradient := by
  rw [show gradient = fun x : Vec 3 => ![x 0,2*x 1,3*x 2] from funext gradient_coordinates]
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

theorem canonicalField_contDiffAt {x : Vec 3} (hx : sqNorm (gradient x) ≠ 0)
    {N : WithTop ℕ∞} : ContDiffAt ℝ N canonicalField x := by
  have hsq : ContDiff ℝ N (fun x => sqNorm (gradient x)) := by
    unfold sqNorm
    apply ContDiff.sum
    intro i hi
    exact ((contDiff_pi.mp gradient_contDiff i).pow 2)
  exact (hsq.contDiffAt.inv hx).smul gradient_contDiff.contDiffAt

theorem canonicalField_pairing {x : Vec 3} (hx : sqNorm (gradient x) ≠ 0) :
    dot (gradient x) (canonicalField x) = 1 := by
  rw [canonicalField,dot_smul_right]
  have he : dot (gradient x) (gradient x) = sqNorm (gradient x) := by
    simp only [dot,sqNorm,pow_two]
  rw [he,inv_mul_cancel₀ hx]

theorem base_gradient : gradient base = ![1,2,3] := by
  simpa [base] using gradient_coordinates base

theorem next_coordinates (ε : ℝ) : next ε = ![1+ε,1,1-(ε+ε^2)/3] := by
  ext i
  fin_cases i <;> simp [next,base,step] <;> ring

theorem next_gradient (ε : ℝ) : gradient (next ε) = ![1+ε,2,3-ε-ε^2] := by
  rw [gradient_coordinates,next_coordinates]
  ext i
  fin_cases i <;> simp <;> ring

theorem gradient_change (ε : ℝ) : change ε = Q.mulVec (step ε) ∧
    change ε = ![ε,0,-(ε+ε^2)] := by
  constructor
  · simp only [change,gradient,next,Matrix.mulVec_add,add_sub_cancel_left]
  · rw [change,next_gradient,base_gradient]
    ext i
    fin_cases i <;> simp <;> ring

theorem base_gradient_sqNorm : sqNorm (gradient base) = 14 := by
  rw [base_gradient]
  norm_num [sqNorm,Fin.sum_univ_succ]

theorem next_gradient_sqNorm_pos (ε : ℝ) : 0 < sqNorm (gradient (next ε)) := by
  rw [next_gradient]
  norm_num [sqNorm,Fin.sum_univ_succ]
  nlinarith [sq_nonneg (1+ε),sq_nonneg (3-ε-ε^2)]

end SpatialQuadraticWarning
end BfgsVerification
