import Mathlib

/-!
# Armijo descent budgets

These scalar lemmas discharge the budget step once an actual objective-level
run supplies Armijo decrease and nonnegative predicted decreases. A lower bound
on objective values along the run suffices; no convergence of iterates or
matrices is assumed. In particular, summability is a conclusion, not a premise.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification.DescentBudget

variable {f d : ℕ → ℝ} {c₁ L : ℝ}

/-- Nonnegative predicted decreases and Armijo imply decreasing objective values. -/
theorem armijo_antitone (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1)) : Antitone f := by
  apply antitone_nat_of_succ_le
  intro k
  have h := hArmijo k
  have hnonneg := mul_nonneg hc₁.le (hd k)
  linarith

/-- Every accepted objective value is in the initial sublevel. -/
theorem armijo_le_initial (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1)) (k : ℕ) : f k ≤ f 0 :=
  armijo_antitone hc₁ hd hArmijo (Nat.zero_le k)

/-- The exact finite Armijo telescope, from any starting index. -/
theorem armijo_sum_mul_le (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (J N : ℕ) : c₁ * (∑ i ∈ Finset.range N, d (J + i)) ≤ f J - f (J + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h := hArmijo (J + N)
    have hidx : J + (N + 1) = J + N + 1 := by omega
    rw [hidx]
    linarith

/-- Finite accepted predicted decreases are controlled by actual decrease. -/
theorem armijo_sum_le (hc₁ : 0 < c₁)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1)) (J N : ℕ) :
    (∑ i ∈ Finset.range N, d (J + i)) ≤ (f J - f (J + N)) / c₁ := by
  apply (le_div_iff₀ hc₁).2
  simpa [mul_comm] using armijo_sum_mul_le hArmijo J N

/-- A lower bound along the run gives a uniform budget for any finite tail. -/
theorem armijo_sum_budget_le (hc₁ : 0 < c₁)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLower : ∀ k, L ≤ f k) (J N : ℕ) :
    (∑ i ∈ Finset.range N, d (J + i)) ≤ (f J - L) / c₁ := by
  apply (armijo_sum_le hc₁ hArmijo J N).trans
  apply div_le_div_of_nonneg_right _ hc₁.le
  linarith [hLower (J + N)]

/-- Armijo and bounded-below objective values imply summability of the budget. -/
theorem armijo_summable (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLower : ∀ k, L ≤ f k) : Summable d := by
  apply summable_of_sum_range_le hd
  intro N
  simpa using armijo_sum_budget_le hc₁ hArmijo hLower 0 N

/-- Infinite tail budgets retain the same bound as their finite truncations. -/
theorem armijo_tail_tsum_le (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLower : ∀ k, L ≤ f k) (J : ℕ) :
    (∑' i, d (J + i)) ≤ (f J - L) / c₁ := by
  apply Real.tsum_le_of_sum_range_le (fun i => hd (J + i))
  exact armijo_sum_budget_le hc₁ hArmijo hLower J

/-- The total predicted-decrease budget is bounded by the initial value gap. -/
theorem armijo_tsum_le (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLower : ∀ k, L ≤ f k) : (∑' k, d k) ≤ (f 0 - L) / c₁ := by
  simpa using armijo_tail_tsum_le hc₁ hd hArmijo hLower 0

/-- Vanishing predicted decreases follow from their derived summability. -/
theorem armijo_tendsto_zero (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLower : ∀ k, L ≤ f k) : Tendsto d atTop (𝓝 0) :=
  (armijo_summable hc₁ hd hArmijo hLower).tendsto_atTop_zero

/-- A finite objective limit is below every value on an Armijo run. -/
theorem armijo_limit_le (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLimit : Tendsto f atTop (𝓝 L)) (k : ℕ) : L ≤ f k := by
  apply le_of_tendsto hLimit
  exact eventually_atTop.2 ⟨k, fun i hi => armijo_antitone hc₁ hd hArmijo hi⟩

/-- The source's finite-limiting-value formulation of summability. -/
theorem armijo_summable_of_tendsto (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLimit : Tendsto f atTop (𝓝 L)) : Summable d :=
  armijo_summable hc₁ hd hArmijo (armijo_limit_le hc₁ hd hArmijo hLimit)

/-- For a finite limiting value, each entire tail is controlled by its value gap. -/
theorem armijo_tail_tsum_le_of_tendsto (hc₁ : 0 < c₁) (hd : ∀ k, 0 ≤ d k)
    (hArmijo : ∀ k, c₁ * d k ≤ f k - f (k + 1))
    (hLimit : Tendsto f atTop (𝓝 L)) (J : ℕ) :
    (∑' i, d (J + i)) ≤ (f J - L) / c₁ :=
  armijo_tail_tsum_le hc₁ hd hArmijo (armijo_limit_le hc₁ hd hArmijo hLimit) J

end BfgsVerification.DescentBudget
