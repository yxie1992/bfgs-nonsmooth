import BfgsVerification.QuadraticGaugeConvex

/-! Actual full-BFGS convergence and the exact Module F logarithmic rate for a
positive-definite quadratic plus a coercive degree-one gauge. All compactness,
gradient bounds, Armijo budgets and correction bounds are derived. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set Asymptotics

namespace BfgsVerification
namespace AdmissibleBFGSRun
open QuadraticGauge

/-- Exact finite-horizon bound with the actual source self-dependent budget. -/
theorem quadraticGauge_finite_budget {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) (N : ℕ) :
    (objective Q γ (R.x N)) ^ 2 * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
      R.referenceEnergy 0 0 + correctionConstant μ Λ *
        ∑ k ∈ Finset.range N, objective Q γ (R.x (k + 1)) := by
  have hmin : ∀ x, objective Q γ 0 ≤ objective Q γ x := by
    simpa only [objective_zero Q γ hh] using objective_nonneg Q hQ γ μ hμ hlower
  have hc := R.quadraticGauge_referenceCorrection Q hQ γ hh μ Λ hμ hlower hupper
  simpa only [objective_zero Q γ hh, sub_zero, valueCorrectionBudget] using
    R.reference_value_budget_bound 0 hmin (correctionConstant μ Λ)
      (by simpa only [objective_zero Q γ hh, sub_zero] using hc) N

/-- Dividing by the actual positive reciprocal sum preserves the explicit
finite-horizon estimate, without an asymptotic constant. -/
theorem quadraticGauge_finite_sqrt_bound {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) {N : ℕ} (hN : 0 < N) :
    objective Q γ (R.x N) ≤ Real.sqrt
      ((R.referenceEnergy 0 0 + correctionConstant μ Λ *
        ∑ k ∈ Finset.range N, objective Q γ (R.x (k + 1))) /
        (∑ k ∈ Finset.range N, (R.q k)⁻¹)) :=
  RateBudgets.sqrt_bound (R.reciprocal_sum_pos hN)
    (R.quadraticGauge_finite_budget Q hQ γ hh μ Λ hμ hlower hupper N)

/-- The exact source instance of both strengthened o(log N/N) and O(log N/N).
Positive definiteness derives compactness; the correction premise is discharged
by the actual quadratic/gauge secant estimate with max(2,1+Λ/μ). -/
theorem quadraticGauge_value_log_orders {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) :
    (fun N => objective Q γ (R.x N)) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∧
    (fun N => objective Q γ (R.x N)) =O[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  have hmin : ∀ x, objective Q γ 0 ≤ objective Q γ x := by
    simpa only [objective_zero Q γ hh] using objective_nonneg Q hQ.posSemidef γ μ hμ hlower
  have hc := R.quadraticGauge_referenceCorrection Q hQ.posSemidef γ hh μ Λ hμ hlower hupper
  simpa only [objective_zero Q γ hh, sub_zero] using
    R.compact_value_log_orders_of_correction_bound 0 hmin
      (R.quadraticGauge_initialSublevel_compact Q hQ γ hh μ hμ hlower)
      (correctionConstant μ Λ) (correctionConstant_nonneg μ Λ)
      (by simpa only [objective_zero Q γ hh, sub_zero] using hc)

/-- Objective and actual accepted iterates converge to the unique minimizer.
No convergence of the BFGS matrices, iterates or step lengths is assumed. -/
theorem quadraticGauge_convergence {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) :
    Tendsto (fun N => objective Q γ (R.x N)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  have hr := (R.quadraticGauge_value_log_orders Q hQ γ hh μ Λ hμ hlower hupper).1
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hv := hr.trans_tendsto hlog
  refine ⟨hv, R.iterates_tendsto_unique_min_of_values 0 ?_ ?_ ?_⟩
  · simpa only [objective_zero Q γ hh] using objective_nonneg Q hQ.posSemidef γ μ hμ hlower
  · intro x hx
    rw [objective_zero Q γ hh] at hx
    exact (objective_eq_zero_iff Q hQ γ hh μ hμ hlower x).mp hx
  · simpa only [objective_zero Q γ hh] using hv

/-- The source's accumulated square-root budget is itself o(log N). The
reciprocal growth input is derived from full BFGS on the compact sublevel. -/
theorem quadraticGauge_sqrt_budget_log_rate {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) :
    Tendsto (fun N : ℕ =>
      Real.sqrt (R.referenceEnergy 0 0 + correctionConstant μ Λ *
        ∑ k ∈ Finset.range N, objective Q γ (R.x (k + 1))) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hmin : ∀ x, objective Q γ 0 ≤ objective Q γ x := by
    simpa only [objective_zero Q γ hh] using objective_nonneg Q hQ.posSemidef γ μ hμ hlower
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel
    (R.quadraticGauge_initialSublevel_compact Q hQ γ hh μ hμ hlower)
  have hs := (objectiveLowerBoundGrowth (m + p) (objective Q γ) R G 0 hG hg
    (fun k => objective_nonneg Q hQ.posSemidef γ μ hμ hlower (R.x k))).2.2.2
  have hc := R.quadraticGauge_referenceCorrection Q hQ.posSemidef γ hh μ Λ hμ hlower hupper
  have h := HarmonicRates.sqrt_budget_log_rate
    (R.valueCorrectionBudget_nonneg 0 hmin (correctionConstant μ Λ)
      (correctionConstant_nonneg μ Λ))
    (fun k => sub_nonneg.mpr (hmin (R.x k))) (correctionConstant_nonneg μ Λ)
    (R.valueCorrectionBudget_step 0 (correctionConstant μ Λ))
    (R.reference_value_budget_bound 0 hmin (correctionConstant μ Λ)
      (by simpa only [objective_zero Q γ hh, sub_zero] using hc)) hs
  simpa only [valueCorrectionBudget, objective_zero Q γ hh, sub_zero] using h

/-- A Euclidean-norm statement of the source family, with the exact norm
convention made explicit rather than relying on the finite-Pi sup norm. -/
theorem quadraticGauge_euclidean_value_log_orders {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) :
    (fun N => objective Q γ (R.x N)) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∧
    (fun N => objective Q γ (R.x N)) =O[atTop]
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) :=
  R.quadraticGauge_value_log_orders Q hQ γ hh μ Λ hμ
    (by simpa only [sqrt_sqNorm_eq_euclidean_norm] using hlower)
    (by simpa only [sqrt_sqNorm_eq_euclidean_norm] using hupper)

end AdmissibleBFGSRun
end BfgsVerification
