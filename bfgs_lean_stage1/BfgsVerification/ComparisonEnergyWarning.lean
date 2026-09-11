import BfgsVerification.EnergyIdentities
import BfgsVerification.ReciprocalGrowth

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.ComparisonEnergyWarning

def reference : Vec 2 := ![1,0]
def moving (k : ℕ) : Vec 2 := ![1,1/((k : ℝ)+1)]
def hessian (k : ℕ) : Mat 2 := Matrix.diagonal ![1,((k : ℝ)+1)^4]

theorem hessian_posDef (k : ℕ) : (hessian k).PosDef := by
  rw [hessian,Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i
  · change (0 : ℝ)<1
    norm_num
  · change (0 : ℝ)<((k : ℝ)+1)^4
    positivity

theorem reference_energy (k : ℕ) : metricEnergy (hessian k) reference=1 := by
  simp [metricEnergy,hessian,reference,Matrix.mulVec_diagonal,dot,Fin.sum_univ_two]

theorem moving_energy (k : ℕ) : metricEnergy (hessian k) (moving k)=1+((k : ℝ)+1)^2 := by
  have hk : (k : ℝ)+1≠0 := by positivity
  simp only [metricEnergy,hessian,moving,Matrix.mulVec_diagonal,dot,Fin.sum_univ_two,
    Pi.mul_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp
  ring

theorem moving_tendsto_reference : Tendsto moving atTop (𝓝 reference) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact tendsto_const_nhds
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem energy_increase_tendsto :
    Tendsto (fun k => metricEnergy (hessian k) (moving k)-metricEnergy (hessian k) reference)
      atTop atTop := by
  simp_rw [moving_energy,reference_energy,add_sub_cancel_left]
  have h : Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_pow_atTop (by decide : (2 : ℕ)≠0)).comp h

/-- Module T's proof warning: an arbitrarily small Euclidean change has no
uniform energy control for positive-definite comparison matrices. This is an
algebraic counterexample to that inference, not an asserted BFGS trajectory. -/
def ComparisonEnergyWarningTarget : Prop :=
  (∀k,(hessian k).PosDef) ∧ Tendsto moving atTop (𝓝 reference) ∧
    (∀k,metricEnergy (hessian k) reference=1) ∧
    Tendsto (fun k => metricEnergy (hessian k) (moving k)-metricEnergy (hessian k) reference)
      atTop atTop

theorem comparisonEnergyWarning : ComparisonEnergyWarningTarget :=
  ⟨hessian_posDef,moving_tendsto_reference,reference_energy,energy_increase_tendsto⟩

end BfgsVerification.ComparisonEnergyWarning
