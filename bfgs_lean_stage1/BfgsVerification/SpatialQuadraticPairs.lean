import BfgsVerification.SpatialQuadraticModel

/-! Actual eligible pairs and the printed scalar identities in C's warning. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace SpatialQuadraticWarning
open TransportedCertificate

def tripleColumns (u v w : Vec 3) : Mat 3 := ![u,v,w]ᵀ

theorem pair_step (ε : ℝ) : pairStep base (next ε) = step ε := by
  simp only [pairStep,next,add_sub_cancel_left]

theorem pair_decrease (ε : ℝ) : pairDecrease base (next ε) (gradient base) = ε^2 := by
  rw [pairDecrease,pair_step,base_gradient]
  simp [dot,step,Fin.sum_univ_succ]
  ring

theorem pair_curvature (ε : ℝ) :
    pairCurvature base (next ε) (gradient base) (gradient (next ε)) =
      ε^2*(ε^2+2*ε+4)/3 := by
  change dot (change ε) (pairStep base (next ε)) = _
  rw [(gradient_change ε).2,pair_step]
  simp [dot,step,Fin.sum_univ_succ]
  ring

theorem objective_decrease (ε : ℝ) :
    objective base-objective (next ε) = ε^2*(2-2*ε-ε^2)/6 := by
  rw [objective_coordinates,objective_coordinates,next_coordinates]
  simp [base]
  ring

theorem actual_pair_eligible {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1/10) :
    EligiblePair objective (1/4) (1/2) base (next ε)
      (gradient base) (gradient (next ε)) := by
  have hsq : 0 < ε^2 := sq_pos_of_pos hε
  have hb : ε^2+2*ε < 1/2 := by
    nlinarith [mul_pos hε (show 0<1/10-ε by linarith)]
  have ha := mul_nonneg hsq.le (show 0≤1/2-2*ε-ε^2 by linarith)
  have ht := mul_nonneg hsq.le (show 0≤ε^2+2*ε+4 by positivity)
  have hw := mul_nonneg hsq.le (show 0≤ε^2+2*ε+4-3/2 by nlinarith)
  refine ⟨objective_hasGradient _,objective_hasGradient _,?_,?_,?_,?_⟩
  · rwa [pair_decrease]
  · rw [pair_decrease,objective_decrease]
    nlinarith
  · rw [pair_decrease,objective_decrease]
    nlinarith
  · rw [pair_decrease,pair_curvature]
    nlinarith

theorem actual_pair_realizable {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1/10) :
    ∃ H : Mat 3, H.PosDef ∧ bfgsStep H (gradient base) 1 = step ε ∧
      metricEnergy H (gradient base) = ε^2 := by
  simpa only [pair_step,pair_decrease] using
    eligible_pair_realizable (actual_pair_eligible hε hsmall)

theorem printed_determinant (ε : ℝ) :
    (tripleColumns (gradient base) (step ε) (change ε)).det =
      (4/3 : ℝ)*ε^2*(1+ε) := by
  rw [base_gradient,(gradient_change ε).2]
  simp [tripleColumns,Matrix.det_transpose,Matrix.det_fin_three,step]
  ring

theorem printed_determinant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (tripleColumns (gradient base) (step ε) (change ε)).det := by
  rw [printed_determinant]
  positivity

theorem determinant_of_linear_combination (g s : Vec 3) (a b : ℝ) :
    (tripleColumns g s (a • g+b • s)).det = 0 := by
  simp [tripleColumns,Matrix.det_transpose,Matrix.det_fin_three]
  ring

end SpatialQuadraticWarning
end BfgsVerification
