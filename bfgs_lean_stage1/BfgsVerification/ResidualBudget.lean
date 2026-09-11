import BfgsVerification.EnergyBudget

/-!
# Scalar residual budgets

The summable-drift scalar part of Module M's residual argument. These results
are conditional on the displayed scalar energy recurrence; they do not yet
derive it from the source's actual smooth subspace and transported frames.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification.ResidualBudget

variable {E q : ℕ → ℝ}

/-- Finite normalization product for nonnegative multiplicative drift. -/
def driftProduct (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 + u k)

@[simp] theorem driftProduct_zero (u : ℕ → ℝ) : driftProduct u 0 = 1 := by
  simp [driftProduct]

@[simp] theorem driftProduct_succ (u : ℕ → ℝ) (N : ℕ) :
    driftProduct u (N + 1) = driftProduct u N * (1 + u N) := by
  simp [driftProduct, Finset.prod_range_succ]

/-- Nonnegative drift has normalization products bounded below by one. -/
theorem one_le_driftProduct {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (N : ℕ) :
    1 ≤ driftProduct u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [driftProduct_succ]
    nlinarith [mul_nonneg (le_trans zero_le_one ih) (hu N)]

/-- Summable drift bounds all products by one explicit exponential constant. -/
theorem driftProduct_le_exp_tsum {u : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hs : Summable u) (N : ℕ) :
    driftProduct u N ≤ Real.exp (∑' k, u k) := by
  calc
    driftProduct u N ≤ ∏ k ∈ Finset.range N, Real.exp (u k) := by
      apply Finset.prod_le_prod
      · intro k _
        linarith [hu k]
      · intro k _
        simpa only [add_comm] using Real.add_one_le_exp (u k)
    _ = Real.exp (∑ k ∈ Finset.range N, u k) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' k, u k) := Real.exp_le_exp.mpr (hs.sum_le_tsum _ (fun k _ => hu k))

/-- A one-sided energy recurrence gives a finite cumulative descent bound. -/
theorem descent_sum_le {U w b : ℕ → ℝ}
    (hU : ∀ k, 0 ≤ U k)
    (hrec : ∀ k, U (k + 1) ≤ U k - w k + b k) (N : ℕ) :
    (∑ k ∈ Finset.range N, w k) ≤ U 0 + ∑ k ∈ Finset.range N, b k := by
  have htel : ∀ N, (∑ k ∈ Finset.range N, w k) ≤
      U 0 - U N + ∑ k ∈ Finset.range N, b k := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hrec M]
  linarith [htel N, hU N]

/-- Scalar normalized residual estimate with its summable drift fully discharged.
The explicit exponential is a uniform bound on the finite normalization products. -/
theorem residual_reciprocal_sum_le {u : ℕ → ℝ} {m C : ℝ}
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hu : ∀ k, 0 ≤ u k) (hs : Summable u) (hm : 0 < m) (hC : 0 ≤ C)
    (hrec : ∀ k, E (k + 1) ≤ (1 + u k) * (E k - m / q k) + C * (k + 1))
    (N : ℕ) :
    (m / Real.exp (∑' k, u k)) * (∑ k ∈ Finset.range N, (q k)⁻¹) ≤
      E 0 + C * ∑ k ∈ Finset.range N, ((k : ℝ) + 1) := by
  let P := driftProduct u
  let B := Real.exp (∑' k, u k)
  have hPone : ∀ k, 1 ≤ P k := one_le_driftProduct hu
  have hPpos : ∀ k, 0 < P k := fun k => lt_of_lt_of_le zero_lt_one (hPone k)
  have hPB : ∀ k, P k ≤ B := driftProduct_le_exp_tsum hu hs
  have hnorm : ∀ k, E (k + 1) / P (k + 1) ≤
      E k / P k - (m / B) * (q k)⁻¹ + C * (k + 1) := by
    intro k
    have hfactor : 0 < 1 + u k := by linarith [hu k]
    have hchange : ((1 + u k) * (E k - m / q k) + C * (k + 1)) / P (k + 1) =
        E k / P k - (m / q k) / P k + C * (k + 1) / P (k + 1) := by
      have hPs : P (k + 1) = P k * (1 + u k) := driftProduct_succ u k
      rw [hPs]
      field_simp [(hPpos k).ne', hfactor.ne', (hq k).ne']
      ring
    have hdescent : (m / B) * (q k)⁻¹ ≤ (m / q k) / P k := by
      calc
        (m / B) * (q k)⁻¹ = (m / q k) / B := by ring
        _ ≤ (m / q k) / P k :=
          div_le_div_of_nonneg_left (div_nonneg hm.le (hq k).le) (hPpos k) (hPB k)
    have hadd : C * (k + 1) / P (k + 1) ≤ C * (k + 1) :=
      div_le_self (by positivity) (hPone (k + 1))
    have hdiv := div_le_div_of_nonneg_right (hrec k) (hPpos (k + 1)).le
    rw [hchange] at hdiv
    linarith
  have hsum := descent_sum_le
    (fun k => div_nonneg (hE k) (hPpos k).le) hnorm N
  simpa only [← Finset.mul_sum, P, driftProduct_zero, div_one, B] using hsum

/-- Summable multiplicative drift and linear additive correction are incompatible
with superquadratic reciprocal growth. This is the scalar contradiction used in
Module M's residual argument; the frame/matrix estimate must still supply `hrec`. -/
theorem residual_recurrence_incompatible {u : ℕ → ℝ} {m C : ℝ}
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hu : ∀ k, 0 ≤ u k) (hs : Summable u) (hm : 0 < m) (hC : 0 ≤ C)
    (hrec : ∀ k, E (k + 1) ≤ (1 + u k) * (E k - m / q k) + C * (k + 1))
    (hS : Tendsto (fun N => (∑ k ∈ Finset.range N, (q k)⁻¹) /
      (N : ℝ) ^ 2) atTop atTop) : False := by
  let B := Real.exp (∑' k, u k)
  have hcoeff : 0 < m / B := div_pos hm (Real.exp_pos _)
  obtain ⟨N, hN, hSN⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hS.eventually (eventually_gt_atTop ((E 0 + C) / (m / B))))).exists
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNsq : 0 < (N : ℝ) ^ 2 := by positivity
  have hsum : (∑ k ∈ Finset.range N, ((k : ℝ) + 1)) ≤ (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      _ = _ := by simp [pow_two]
  have hfinite := residual_reciprocal_sum_le hE hq hu hs hm hC hrec N
  have hquad : (m / B) * (∑ k ∈ Finset.range N, (q k)⁻¹) ≤
      (E 0 + C) * (N : ℝ) ^ 2 := by
    have hCs := mul_le_mul_of_nonneg_left hsum hC
    have hE0 := mul_le_mul_of_nonneg_left (show 1 ≤ (N : ℝ) ^ 2 by nlinarith) (hE 0)
    dsimp only [B]
    nlinarith
  have hnormalized : (m / B) * ((∑ k ∈ Finset.range N, (q k)⁻¹) /
      (N : ℝ) ^ 2) ≤ E 0 + C := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hNsq).2 hquad
  have hupper : ((∑ k ∈ Finset.range N, (q k)⁻¹) / (N : ℝ) ^ 2) ≤
      (E 0 + C) / (m / B) := by
    apply (le_div_iff₀ hcoeff).2
    simpa only [mul_comm] using hnormalized
  exact not_lt_of_ge hupper hSN

end BfgsVerification.ResidualBudget
