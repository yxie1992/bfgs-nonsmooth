import BfgsVerification.EnergyBudget

/-! Scalar rate consequences of explicit energy budgets. Objective-level
wrappers must derive these budgets and superquadratic growth from actual BFGS. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification
namespace RateBudgets

/-- A finite energy inequality gives the exact square-root bound at each
positive horizon. -/
theorem sqrt_bound {a S E : ℝ} (hS : 0 < S) (h : a ^ 2 * S ≤ E) :
    a ≤ Real.sqrt (E / S) :=
  Real.le_sqrt_of_sq_le ((le_div_iff₀ hS).2 h)

/-- A quadratic bound for a scaled gap vanishes against a superquadratic
reciprocal sum. The bound need only hold eventually. -/
theorem scaled_gap_tendsto_zero {a S : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) (C : ℝ)
    (hb : ∀ᶠ N in atTop, (a N) ^ 2 * S N ≤ C * (N : ℝ) ^ 2) :
    Tendsto a atTop (𝓝 0) := by
  have hS' := EnergyBudget.tendsto_atTop_of_superquadratic hS
  have hu : Tendsto (fun N : ℕ => C * (N : ℝ) ^ 2 / S N) atTop (𝓝 0) := by
    simpa only [div_div_eq_mul_div] using hS.const_div_atTop C
  have hs : Tendsto (fun N => (a N) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg (a N)) _ hu
    filter_upwards [hb, hS'.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hp
    exact (le_div_iff₀ hp).2 hN
  simpa only [Real.sqrt_sq (ha _), Real.sqrt_zero] using hs.sqrt

/-- A linear cumulative correction budget gives gap=o(N^(-1/2)). This
formulation states the equivalent limit sqrt(N)*gap(N)→0. -/
theorem linear_budget_rate {gap S T : ℕ → ℝ} {E C : ℝ}
    (hg : ∀ N, 0 ≤ gap N)
    (hb : ∀ N, (gap N) ^ 2 * S N ≤ E + T N)
    (hT : ∀ᶠ N in atTop, T N ≤ C * (N : ℝ))
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * gap N) atTop (𝓝 0) := by
  apply scaled_gap_tendsto_zero (fun N => mul_nonneg (Real.sqrt_nonneg _) (hg N))
    hS (|E| + |C|)
  filter_upwards [hT, eventually_ge_atTop (1 : ℕ)] with N hTN hN
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hb' : (gap N) ^ 2 * S N ≤ |E| + |C| * (N : ℝ) := by
    exact ((hb N).trans (add_le_add_left hTN E)).trans
      (add_le_add (le_abs_self E) (mul_le_mul_of_nonneg_right (le_abs_self C) hn0))
  have hm := mul_le_mul_of_nonneg_left hb' hn0
  rw [mul_pow, Real.sq_sqrt hn0]
  nlinarith [mul_nonneg (abs_nonneg E) (sub_nonneg.mpr hn)]

/-- A bounded cumulative energy budget gives gap=o(N^(-1)), in its
exact equivalent form N*gap(N)→0. -/
theorem bounded_budget_rate {gap S : ℕ → ℝ} {E : ℝ}
    (hg : ∀ N, 0 ≤ gap N) (hb : ∀ N, (gap N) ^ 2 * S N ≤ E)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * gap N) atTop (𝓝 0) := by
  apply scaled_gap_tendsto_zero (fun N => mul_nonneg (Nat.cast_nonneg N) (hg N)) hS E
  exact Eventually.of_forall fun N => by
    have hm := mul_le_mul_of_nonneg_left (hb N) (sq_nonneg (N : ℝ))
    nlinarith

end RateBudgets
end BfgsVerification
