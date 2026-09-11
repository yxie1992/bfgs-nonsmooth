import BfgsVerification.HomogeneousLowRankConvergence
import BfgsVerification.QuadraticGaugeAlgebra

/-! The displayed H.5.3 potential budgets and pointwise alternative argument.
These are retained deductions even though H.A uses a different proved route. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem homogeneous_potential_antitone (hF : Homogeneous.PositiveDegreeOne F) :
    Antitone R.homogeneousPotential := by
  apply antitone_nat_of_succ_le
  intro k
  have hp := R.homogeneous_potential_step hF k
  have hn : 0 ≤ (F (R.x k))^2 / R.q k := div_nonneg (sq_nonneg _) (R.q_pos k).le
  linarith

/-- H.5.3's actual energy bound M=Φ₀−γL follows from a lower value bound only. -/
theorem homogeneous_energy_bound_of_lower_bound (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) (k : ℕ) :
    R.referenceEnergy 0 k ≤ R.homogeneousPotential 0 - ((1-R.c₁)/R.c₁)*L := by
  have hp := R.homogeneous_potential_antitone hF (Nat.zero_le k)
  have hc : 0 ≤ (1-R.c₁)/R.c₁ :=
    div_nonneg (sub_nonneg.mpr (R.c₁_lt_c₂.trans R.c₂_lt_one).le) R.c₁_pos.le
  have hl := mul_le_mul_of_nonneg_left (hL k) hc
  change R.referenceEnergy 0 k + ((1-R.c₁)/R.c₁)*F (R.x k) ≤ R.homogeneousPotential 0 at hp
  linarith

/-- The finite weighted reciprocal budget retains the source's exact γL term. -/
theorem homogeneous_weighted_sum_budget (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) (N : ℕ) :
    (∑ k ∈ Finset.range N, (F (R.x k))^2 / R.q k) ≤
      R.homogeneousPotential 0 - ((1-R.c₁)/R.c₁)*L := by
  have hacc : ∀ N, (∑ k ∈ Finset.range N, (F (R.x k))^2 / R.q k) +
      R.homogeneousPotential N ≤ R.homogeneousPotential 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [R.homogeneous_potential_step hF N]
  have hc : 0 ≤ (1-R.c₁)/R.c₁ :=
    div_nonneg (sub_nonneg.mpr (R.c₁_lt_c₂.trans R.c₂_lt_one).le) R.c₁_pos.le
  have hl := mul_le_mul_of_nonneg_left (hL N) hc
  have hE := R.referenceEnergy_nonneg 0 N
  have hsum := hacc N
  change (∑ k ∈ Finset.range N, (F (R.x k))^2 / R.q k) +
    (R.referenceEnergy 0 N + ((1-R.c₁)/R.c₁)*F (R.x N)) ≤ R.homogeneousPotential 0 at hsum
  linarith

theorem homogeneous_weighted_summable (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) :
    Summable (fun k => (F (R.x k))^2 / R.q k) := by
  apply summable_of_sum_range_le (fun k => div_nonneg (sq_nonneg _) (R.q_pos k).le)
  exact R.homogeneous_weighted_sum_budget hF L hL

theorem homogeneous_weighted_tsum_budget (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) :
    (∑' k, (F (R.x k))^2 / R.q k) ≤ R.homogeneousPotential 0 - ((1-R.c₁)/R.c₁)*L := by
  apply Real.tsum_le_of_sum_range_le (fun k => div_nonneg (sq_nonneg _) (R.q_pos k).le)
  exact R.homogeneous_weighted_sum_budget hF L hL

/-- Euler plus actual SPD metric Cauchy–Schwarz yields the displayed pointwise
H.5.3 bound, without any uniform spectral bound. -/
theorem homogeneous_value_sq_le_energy_mul_q (hF : Homogeneous.PositiveDegreeOne F) (k : ℕ) :
    (F (R.x k))^2 ≤ R.referenceEnergy 0 k * R.q k := by
  have hH := R.positive_definite k
  have hB := hH.inv
  have hi : (R.H k)⁻¹.mulVec ((R.H k).mulVec (R.g k)) = R.g k := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH.det_pos.ne'.isUnit, Matrix.one_mulVec]
  have he : metricEnergy (R.H k)⁻¹ ((R.H k).mulVec (R.g k)) = R.q k := by
    unfold metricEnergy
    rw [hi]
    exact dotProduct_comm _ _
  have h := QuadraticGauge.metric_cauchy_schwarz hB.posSemidef ((R.H k).mulVec (R.g k)) (R.x k)
  rw [hi, he, R.homogeneous_euler hF] at h
  simpa only [referenceEnergy, sub_zero, hessian, mul_comm] using h

/-- The source's direct pointwise budget F_k²≤Mq_k is a derived actual-run
statement with M=Φ₀−γL. -/
theorem homogeneous_value_sq_le_budget_mul_q (hF : Homogeneous.PositiveDegreeOne F)
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) (k : ℕ) :
    (F (R.x k))^2 ≤ (R.homogeneousPotential 0 - ((1-R.c₁)/R.c₁)*L)*R.q k :=
  (R.homogeneous_value_sq_le_energy_mul_q hF k).trans
    (mul_le_mul_of_nonneg_right (R.homogeneous_energy_bound_of_lower_bound hF L hL k) (R.q_pos k).le)

end AdmissibleBFGSRun
end BfgsVerification
