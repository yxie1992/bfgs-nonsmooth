import BfgsVerification.HarmonicRates
import BfgsVerification.ObjectiveRates

/-! The actual full-BFGS logarithmic rate criterion. The explicit pointwise
correction estimate remains an objective-specific premise in this module. -/

noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics

namespace BfgsVerification
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The source quadratic-plus-gauge accumulated budget, with the actual
reference energy and actual accepted objective gaps. -/
def valueCorrectionBudget (star : Vec n) (C : ℝ) (N : ℕ) : ℝ :=
  R.referenceEnergy star 0 + C * ∑ k ∈ Finset.range N, (F (R.x (k + 1)) - F star)

theorem valueCorrectionBudget_nonneg (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) : 0 ≤ R.valueCorrectionBudget star C N := by
  exact add_nonneg (R.referenceEnergy_nonneg star 0)
    (mul_nonneg hC (Finset.sum_nonneg (fun k _ => sub_nonneg.mpr (hmin _))))

theorem valueCorrectionBudget_step (star : Vec n) (C : ℝ) (N : ℕ) :
    R.valueCorrectionBudget star C (N + 1) = R.valueCorrectionBudget star C N +
      C * (F (R.x (N + 1)) - F star) := by
  simp only [valueCorrectionBudget, Finset.sum_range_succ]
  ring

theorem reference_value_budget_bound (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (C : ℝ) (hcor : ∀ k, R.referenceCorrection star k ≤ C * (F (R.x (k + 1)) - F star))
    (N : ℕ) :
    (F (R.x N) - F star) ^ 2 * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.valueCorrectionBudget star C N := by
  apply (R.fixed_reference_energy_bound star hmin N).trans
  apply add_le_add_left
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => hcor k)

/-- Exact reference-energy recurrence plus an actual correction estimate gives
both o(log N/N) and the weaker source O(log N/N) rate. -/
theorem value_log_orders_of_correction_bound (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (G : ℝ) (hG : 0 < G)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (C : ℝ) (hC : 0 ≤ C)
    (hcor : ∀ k, R.referenceCorrection star k ≤ C * (F (R.x (k + 1)) - F star)) :
    (fun N => F (R.x N) - F star) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∧
    (fun N => F (R.x N) - F star) =O[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  have hs := (objectiveLowerBoundGrowth n F R G (F star) hG hg
    (fun k => hmin (R.x k))).2.2.2
  exact HarmonicRates.self_budget_value_log_orders
    (R.valueCorrectionBudget_nonneg star hmin C hC)
    (fun k => sub_nonneg.mpr (hmin _)) hC (R.valueCorrectionBudget_step star C)
    (R.reference_value_budget_bound star hmin C hcor) hs

/-- Compactness derives the gradient bounds and Armijo budget in the criterion. -/
theorem compact_value_log_orders_of_correction_bound (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (hK : IsCompact R.initialSublevel)
    (C : ℝ) (hC : 0 ≤ C)
    (hcor : ∀ k, R.referenceCorrection star k ≤ C * (F (R.x (k + 1)) - F star)) :
    (fun N => F (R.x N) - F star) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∧
    (fun N => F (R.x N) - F star) =O[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  exact R.value_log_orders_of_correction_bound star hmin G hG hg C hC hcor

end AdmissibleBFGSRun
end BfgsVerification
