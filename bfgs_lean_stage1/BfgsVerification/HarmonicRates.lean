import BfgsVerification.RateBudgets

/-! Logarithmic growth from little-o harmonic increments, including the finite
initial prefix. These are analytic helpers, not assumed BFGS recurrences. -/

noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics

namespace BfgsVerification
namespace HarmonicRates

theorem harmonic_sum_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ Finset.range N, ((k : ℝ) + 1)⁻¹ := by
  simp [harmonic]

theorem log_nat_tendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem harmonic_sum_tendsto :
    Tendsto (fun N => ∑ k ∈ Finset.range N, ((k : ℝ) + 1)⁻¹) atTop atTop := by
  apply tendsto_atTop_mono (fun N => ?_)
    (log_nat_tendsto.comp (tendsto_add_atTop_nat 1))
  simpa only [harmonic_sum_real] using log_add_one_le_harmonic N

theorem harmonic_sum_isBigO_log :
    (fun N => ∑ k ∈ Finset.range N, ((k : ℝ) + 1)⁻¹) =O[atTop]
      (fun N : ℕ => Real.log (N : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨2, ?_⟩
  filter_upwards [log_nat_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
  have hs : 0 ≤ ∑ k ∈ Finset.range N, ((k : ℝ) + 1)⁻¹ :=
    Finset.sum_nonneg (fun k _ => by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hs, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hb := harmonic_le_one_add_log N
  rw [harmonic_sum_real] at hb
  linarith

/-- If N times the successive increment tends to zero, the whole sequence
is o(log N). No sign or monotonicity premise is needed for this analytic fact. -/
theorem log_rate_of_harmonic_increments {a : ℕ → ℝ}
    (hinc : Tendsto (fun N : ℕ => ((N : ℝ) + 1) * (a (N + 1) - a N))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => a N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hsmall : (fun N => a (N + 1) - a N) =o[atTop]
      (fun N : ℕ => ((N : ℝ) + 1)⁻¹) := by
    apply isLittleO_of_tendsto (fun (N : ℕ) hn => False.elim ((by positivity :
      ((N : ℝ) + 1)⁻¹ ≠ 0) hn))
    simpa only [div_inv_eq_mul, mul_comm] using hinc
  have hs := (hsmall.sum_range (fun k => by positivity) harmonic_sum_tendsto).trans_isBigO
    harmonic_sum_isBigO_log
  have hc : (fun _N : ℕ => a 0) =o[atTop] (fun N : ℕ => Real.log (N : ℝ)) := by
    apply isLittleO_const_left.mpr
    right
    exact log_nat_tendsto.congr' (log_nat_tendsto.eventually
      (eventually_ge_atTop (0 : ℝ)) |>.mono fun _ h => (Real.norm_of_nonneg h).symm)
  have ha : a =o[atTop] (fun N : ℕ => Real.log (N : ℝ)) := by
    convert hs.add hc using 1
    ext N
    rw [Finset.sum_range_sub]
    ring
  apply (isLittleO_iff_tendsto' ?_).mp ha
  filter_upwards [log_nat_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
  exact fun he => False.elim (hN.ne' he)

/-- Exact scalar square-root increment bound; includes a vanishing new budget. -/
theorem sqrt_increment_bound {A B C f S : ℝ}
    (hA : 0 ≤ A) (hf : 0 ≤ f) (hC : 0 ≤ C) (hS : 0 < S)
    (hrec : B = A + C * f) (hb : f ^ 2 * S ≤ B) :
    0 ≤ Real.sqrt B - Real.sqrt A ∧
      Real.sqrt B - Real.sqrt A ≤ C / Real.sqrt S := by
  have hAB : A ≤ B := by nlinarith
  have hB : 0 ≤ B := hA.trans hAB
  have hD : 0 ≤ Real.sqrt B - Real.sqrt A :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hAB)
  refine ⟨hD, ?_⟩
  have hs := Real.sqrt_pos.mpr hS
  have hfs : f * Real.sqrt S ≤ Real.sqrt B := by
    have hsq : (f * Real.sqrt S) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS.le, Real.sq_sqrt hB]
      exact hb
    nlinarith [Real.sqrt_nonneg B, mul_nonneg hf hs.le]
  have hid : (Real.sqrt B - Real.sqrt A) *
      (Real.sqrt B + Real.sqrt A) = C * f := by
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
  by_cases hu : Real.sqrt B = 0
  · have hv : Real.sqrt A = 0 := by nlinarith [Real.sqrt_nonneg A]
    rw [hu, hv, sub_self]
    exact div_nonneg hC hs.le
  have hup : 0 < Real.sqrt B := lt_of_le_of_ne (Real.sqrt_nonneg B) (Ne.symm hu)
  apply (le_div_iff₀ hs).2
  have hd : (Real.sqrt B - Real.sqrt A) * Real.sqrt B ≤ C * f := by
    nlinarith [mul_nonneg hD (Real.sqrt_nonneg A)]
  have hm := mul_le_mul_of_nonneg_right hd hs.le
  have hn := mul_le_mul_of_nonneg_left hfs hC
  nlinarith

/-- Superquadratic reciprocal sums give N/sqrt(S_N)→0, including their
standard totalized values at the zero horizon. -/
theorem inverse_sqrt_scale_tendsto {S : ℕ → ℝ}
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.sqrt (S N)) atTop (𝓝 0) := by
  have h := (hS.const_div_atTop 1).sqrt
  simpa only [one_div, inv_div, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _), Real.sqrt_zero] using h

/-- Exact recurrence plus the energy bound forces the square-root budget to
be o(log N). Nonnegative initial budgets include the zero-budget case. -/
theorem sqrt_budget_log_rate {A f S : ℕ → ℝ} {C : ℝ}
    (hA : ∀ N, 0 ≤ A N) (hf : ∀ N, 0 ≤ f N) (hC : 0 ≤ C)
    (hrec : ∀ N, A (N + 1) = A N + C * f (N + 1))
    (hb : ∀ N, (f N) ^ 2 * S N ≤ A N)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun N : ℕ => Real.sqrt (A N) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  apply log_rate_of_harmonic_increments
  have hu := ((inverse_sqrt_scale_tendsto hS).comp (tendsto_add_atTop_nat 1)).const_mul C
  have hs := (EnergyBudget.tendsto_atTop_of_superquadratic hS).comp
    (tendsto_add_atTop_nat 1)
  apply squeeze_zero' ?_ ?_ (by simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using hu)
  · exact Eventually.of_forall fun N => mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.sqrt_le_sqrt (by rw [hrec]; exact le_add_of_nonneg_right (mul_nonneg hC (hf _)))))
  · filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with N hSN
    have hi := (sqrt_increment_bound (hA N) (hf (N + 1)) hC hSN
      (hrec N) (hb (N + 1))).2
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (N : ℝ) + 1)
    convert hm using 1 <;> simp only [Function.comp_apply] <;> ring

/-- A budget growing by C*f and the actual energy inequality give
f_N=o(log(N)/N). The finite prefix is included by the harmonic sum theorem. -/
theorem self_budget_value_log_rate {A f S : ℕ → ℝ} {C : ℝ}
    (hA : ∀ N, 0 ≤ A N) (hf : ∀ N, 0 ≤ f N) (hC : 0 ≤ C)
    (hrec : ∀ N, A (N + 1) = A N + C * f (N + 1))
    (hb : ∀ N, (f N) ^ 2 * S N ≤ A N)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * f N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hu := sqrt_budget_log_rate hA hf hC hrec hb hS
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [log_nat_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with N hlog
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf N)) hlog.le
  · filter_upwards [hS.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop (0 : ℕ),
      log_nat_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with N hSN hN hlog
    have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hSN' : (N : ℝ) ^ 2 ≤ S N := by
      have h := (le_div_iff₀ (sq_pos_of_pos hn)).mp hSN
      simpa using h
    apply div_le_div_of_nonneg_right _ hlog.le
    apply Real.le_sqrt_of_sq_le
    have hm := mul_le_mul_of_nonneg_left hSN' (sq_nonneg (f N))
    nlinarith [hb N]

/-- The conventional little-o and big-O notation follows from the scaled
limit; the zero and one horizons do not affect either asymptotic assertion. -/
theorem self_budget_value_log_orders {A f S : ℕ → ℝ} {C : ℝ}
    (hA : ∀ N, 0 ≤ A N) (hf : ∀ N, 0 ≤ f N) (hC : 0 ≤ C)
    (hrec : ∀ N, A (N + 1) = A N + C * f (N + 1))
    (hb : ∀ N, (f N) ^ 2 * S N ≤ A N)
    (hS : Tendsto (fun N => S N / (N : ℝ) ^ 2) atTop atTop) :
    f =o[atTop] (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) ∧
    f =O[atTop] (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  have hl : f =o[atTop] (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
    apply isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℕ),
        log_nat_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hlog
      have hp : 0 < Real.log (N : ℝ) / (N : ℝ) := div_pos hlog (Nat.cast_pos.mpr hN)
      exact fun he => False.elim (hp.ne' he)
    · simpa only [div_div_eq_mul_div, mul_comm] using
        self_budget_value_log_rate hA hf hC hrec hb hS
  exact ⟨hl, hl.isBigO⟩

end HarmonicRates
end BfgsVerification
