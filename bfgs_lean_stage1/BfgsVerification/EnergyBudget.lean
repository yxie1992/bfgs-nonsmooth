import Mathlib

/-!
# Fixed-reference energy budgets

Scalar telescoping and asymptotic consequences of Module M's exact energy
identity. The exact identity remains an explicit input here; objective-level
exports must supply it from the actual Hessian BFGS update. No convergence of
iterates or matrices is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification.EnergyBudget

variable {E q a R gap : ℕ → ℝ}

/-- The complete finite telescope retains the terminal energy. -/
theorem energy_telescope
    (hrec : ∀ k, E (k + 1) = E k - (a k) ^ 2 / q k + R k) (N : ℕ) :
    (∑ k ∈ Finset.range N, (a k) ^ 2 / q k) =
      E 0 - E N + ∑ k ∈ Finset.range N, R k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hrec N]
    ring

/-- Source M:energybound follows from the exact recurrence and convex gap bound. -/
theorem gap_sq_mul_reciprocal_sum_le
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hgap : ∀ k, 0 ≤ gap k) (hmono : Antitone gap)
    (ha : ∀ k, gap k ≤ a k)
    (hrec : ∀ k, E (k + 1) = E k - (a k) ^ 2 / q k + R k) (N : ℕ) :
    (gap N) ^ 2 * (∑ k ∈ Finset.range N, (q k)⁻¹) ≤
      E 0 + ∑ k ∈ Finset.range N, R k := by
  calc
    (gap N) ^ 2 * (∑ k ∈ Finset.range N, (q k)⁻¹) =
        ∑ k ∈ Finset.range N, (gap N) ^ 2 * (q k)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range N, (a k) ^ 2 / q k := by
      apply Finset.sum_le_sum
      intro k hk
      have hle : gap N ≤ a k := (hmono (Nat.le_of_lt (Finset.mem_range.mp hk))).trans (ha k)
      have hs : (gap N) ^ 2 ≤ (a k) ^ 2 := by nlinarith [hgap N]
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (hq k).le)
    _ = E 0 - E N + ∑ k ∈ Finset.range N, R k := energy_telescope hrec N
    _ ≤ E 0 + ∑ k ∈ Finset.range N, R k := by linarith [hE N]

/-- A vanishing normalized energy budget forces any nonnegative gap to vanish. -/
theorem gap_tendsto_zero_of_normalized_budget {S T : ℕ → ℝ} {E₀ : ℝ}
    (hgap : ∀ k, 0 ≤ gap k)
    (hbound : ∀ N, (gap N) ^ 2 * S N ≤ E₀ + T N)
    (hS : Tendsto S atTop atTop)
    (hT : Tendsto (fun N => T N / S N) atTop (𝓝 0)) :
    Tendsto gap atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (E₀ + T N) / S N) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using (hS.const_div_atTop E₀).add hT
  have hsq : Tendsto (fun N => (gap N) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg (gap N)) _ hupper
    filter_upwards [hS.eventually (eventually_gt_atTop (0 : ℝ))] with N hpos
    exact (le_div_iff₀ hpos).2 (hbound N)
  simpa only [Real.sqrt_sq (hgap _), Real.sqrt_zero] using hsq.sqrt

/-- The exact energy identity proves the little-o cumulative-correction criterion. -/
theorem energy_gap_tendsto_zero
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hgap : ∀ k, 0 ≤ gap k) (hmono : Antitone gap)
    (ha : ∀ k, gap k ≤ a k)
    (hrec : ∀ k, E (k + 1) = E k - (a k) ^ 2 / q k + R k)
    (hS : Tendsto (fun N => ∑ k ∈ Finset.range N, (q k)⁻¹) atTop atTop)
    (hR : Tendsto (fun N => (∑ k ∈ Finset.range N, R k) /
      (∑ k ∈ Finset.range N, (q k)⁻¹)) atTop (𝓝 0)) :
    Tendsto gap atTop (𝓝 0) :=
  gap_tendsto_zero_of_normalized_budget hgap
    (gap_sq_mul_reciprocal_sum_le hE hq hgap hmono ha hrec) hS hR

/-- Superquadratic divergence implies divergence of the unnormalized sums. -/
theorem tendsto_atTop_of_superquadratic {S : ℕ → ℝ}
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto S atTop atTop := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  apply (hS.atTop_mul_atTop₀ hpow).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  exact div_mul_cancel₀ (S N) hn

/-- An eventual quadratic upper budget suffices against superquadratic growth.
Corrections need not be termwise nonnegative for this scalar consequence. -/
theorem gap_tendsto_zero_of_quadratic_budget {S T : ℕ → ℝ} {E₀ C : ℝ}
    (hgap : ∀ k, 0 ≤ gap k)
    (hbound : ∀ N, (gap N) ^ 2 * S N ≤ E₀ + T N)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop)
    (hT : ∀ᶠ N in atTop, T N ≤ C * (N : ℝ) ^ 2) :
    Tendsto gap atTop (𝓝 0) := by
  have hSdiv := tendsto_atTop_of_superquadratic hS
  have hquad : Tendsto (fun N : ℕ => C * (N : ℝ) ^ 2 / S N) atTop (𝓝 0) := by
    simpa only [div_div_eq_mul_div] using hS.const_div_atTop C
  have hupper : Tendsto (fun N : ℕ => (E₀ + C * (N : ℝ) ^ 2) / S N) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using (hSdiv.const_div_atTop E₀).add hquad
  have hsq : Tendsto (fun N => (gap N) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg (gap N)) _ hupper
    filter_upwards [hSdiv.eventually (eventually_gt_atTop (0 : ℝ)), hT] with N hpos hTN
    apply (le_div_iff₀ hpos).2
    exact (hbound N).trans (add_le_add_left hTN E₀)
  simpa only [Real.sqrt_sq (hgap _), Real.sqrt_zero] using hsq.sqrt

/-- Module M's quadratic-correction consequence, discharged from the exact energy identity. -/
theorem energy_gap_tendsto_zero_of_quadratic_corrections {C : ℝ}
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k)
    (hgap : ∀ k, 0 ≤ gap k) (hmono : Antitone gap)
    (ha : ∀ k, gap k ≤ a k)
    (hrec : ∀ k, E (k + 1) = E k - (a k) ^ 2 / q k + R k)
    (hS : Tendsto (fun N => (∑ k ∈ Finset.range N, (q k)⁻¹) /
      (N : ℝ) ^ 2) atTop atTop)
    (hR : ∀ᶠ N in atTop, (∑ k ∈ Finset.range N, R k) ≤ C * (N : ℝ) ^ 2) :
    Tendsto gap atTop (𝓝 0) :=
  gap_tendsto_zero_of_quadratic_budget hgap
    (gap_sq_mul_reciprocal_sum_le hE hq hgap hmono ha hrec) hS hR

end BfgsVerification.EnergyBudget
