import BfgsVerification.Definitions
import BfgsVerification.ScalarHierarchy

/-!
# Reciprocal growth from an explicit scalar hierarchy

STATUS: compiled with the pinned Lean 4.19.0 / mathlib environment.

The final theorem in this file is CONDITIONAL on `NormalizedHierarchy`. It must
not be described as an end-to-end BFGS theorem until the matrix-to-hierarchy
bridge is proved. All constants and quantified tails are explicit.

The proof is a logarithmic rendering of M.2's weighted-potential argument.
The arithmetic mean follows from log(u) <= u - 1; this avoids an additional
AM--GM dependency for the qualitative divergence assertion.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace BfgsVerification.ReciprocalGrowth

open BfgsVerification.ScalarHierarchy

def logReciprocalMean (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  -(∑ k ∈ Finset.range N, Real.log (q k)) / (N : ℝ)

/-- A finite-prefix identity used to avoid silently dropping the initial terms. -/
theorem sum_prefix_tail (f : ℕ → ℝ) (J m : ℕ) :
    (∑ k ∈ Finset.range (J + m), f k) =
      (∑ k ∈ Finset.range J, f k) +
        ∑ k ∈ Finset.range m, f (J + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- Telescoping logarithms of q_k V_{k+1} <= A V_k, on one fixed tail. -/
theorem log_potential_telescope
    (q V : ℕ → ℝ) (A : ℝ) (J : ℕ)
    (hq : ∀ k, 0 < q k) (hV : ∀ k, 0 < V k) (hA : 0 < A)
    (hstep : ∀ k, J ≤ k → q k * V (k + 1) ≤ A * V k) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m, Real.log (q (J + k))) + Real.log (V (J + m)) ≤
        Real.log (V J) + (m : ℝ) * Real.log A := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hk : J ≤ J + m := Nat.le_add_right J m
      have hlog := Real.log_le_log
        (mul_pos (hq (J + m)) (hV (J + m + 1))) (hstep (J + m) hk)
      rw [Real.log_mul (ne_of_gt (hq (J + m))) (ne_of_gt (hV (J + m + 1))),
        Real.log_mul (ne_of_gt hA) (ne_of_gt (hV (J + m)))] at hlog
      rw [Finset.sum_range_succ, Nat.cast_succ]
      have hidx : J + (m + 1) = J + m + 1 := by omega
      rw [hidx]
      nlinarith [ih, hlog]

/-- Use q at the last index to remove V at the last index. -/
theorem tail_log_product_upper
    (q V : ℕ → ℝ) (A C : ℝ) (J m : ℕ)
    (hq : ∀ k, 0 < q k) (hV : ∀ k, 0 < V k)
    (hA : 0 < A) (hC : 0 < C)
    (hstep : ∀ k, J ≤ k → q k * V (k + 1) ≤ A * V k)
    (hbound : ∀ k, q k ≤ C * V k) :
    (∑ k ∈ Finset.range (m + 1), Real.log (q (J + k))) ≤
      Real.log C + Real.log (V J) + (m : ℝ) * Real.log A := by
  have ht := log_potential_telescope q V A J hq hV hA hstep m
  have hb := Real.log_le_log (hq (J + m)) (hbound (J + m))
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (hV (J + m)))] at hb
  rw [Finset.sum_range_succ]
  linarith

/-- Restore the fixed prefix explicitly; all its effect is in B. -/
theorem global_log_product_upper
    (q V : ℕ → ℝ) (A C : ℝ) (J : ℕ)
    (hq : ∀ k, 0 < q k) (hV : ∀ k, 0 < V k)
    (hA : 0 < A) (hC : 0 < C)
    (hstep : ∀ k, J ≤ k → q k * V (k + 1) ≤ A * V k)
    (hbound : ∀ k, q k ≤ C * V k) :
    ∃ B : ℝ, ∀ N : ℕ, J + 1 ≤ N →
      (∑ k ∈ Finset.range N, Real.log (q k)) ≤ B + (N : ℝ) * Real.log A := by
  let B : ℝ := (∑ k ∈ Finset.range J, Real.log (q k)) +
    Real.log C + Real.log (V J) - ((J : ℝ) + 1) * Real.log A
  refine ⟨B, ?_⟩
  intro N hN
  let m := N - (J + 1)
  have hNm : N = J + (m + 1) := by dsimp [m]; omega
  have ht := tail_log_product_upper q V A C J m hq hV hA hC hstep hbound
  rw [hNm, sum_prefix_tail]
  dsimp [B]
  push_cast
  nlinarith [ht]

/-- Arbitrarily small fixed tail-contraction factors force divergence of
    the logarithmic reciprocal mean. -/
theorem tail_potentials_force_log_growth
    (q : ℕ → ℝ) (C : ℝ)
    (hq : ∀ k, 0 < q k) (hC : 0 < C)
    (hpot : ∀ A : ℝ, 0 < A →
      ∃ J : ℕ, ∃ V : ℕ → ℝ,
        (∀ k, 0 < V k) ∧
        (∀ k, J ≤ k → q k * V (k + 1) ≤ A * V k) ∧
        (∀ k, q k ≤ C * V k)) :
    Tendsto (logReciprocalMean q) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro target
  let A := Real.exp (-(target + 1))
  have hA : 0 < A := Real.exp_pos _
  obtain ⟨J, V, hV, hstep, hbound⟩ := hpot A hA
  obtain ⟨B, hB⟩ := global_log_product_upper q V A C J hq hV hA hC hstep hbound
  obtain ⟨M, hM⟩ := exists_nat_gt B
  refine ⟨max (J + 1) M, ?_⟩
  intro N hN
  have hJN : J + 1 ≤ N := le_trans (le_max_left _ _) hN
  have hMN : M ≤ N := le_trans (le_max_right _ _) hN
  have hNR : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hBN : B ≤ (N : ℝ) := by
    exact le_trans hM.le (by exact_mod_cast hMN)
  have hsum := hB N hJN
  have hlogA : Real.log A = -(target + 1) := by
    dsimp [A]
    exact Real.log_exp _
  rw [hlogA] at hsum
  change target ≤ -(∑ k ∈ Finset.range N, Real.log (q k)) / (N : ℝ)
  apply (le_div_iff₀ hNR).2
  nlinarith [hsum, hBN]

/-- The logarithmic convention agrees with the actual product-root expression. -/
theorem geometricMean_eq_exp_logMean
    (q : ℕ → ℝ) (hq : ∀ k, 0 < q k) (N : ℕ) :
    reciprocalGeometricMean q N = Real.exp (logReciprocalMean q N) := by
  have hprod : 0 < ∏ k ∈ Finset.range N, (q k)⁻¹ :=
    Finset.prod_pos (fun k _ => inv_pos.mpr (hq k))
  unfold reciprocalGeometricMean
  rw [Real.rpow_def_of_pos hprod]
  rw [Real.log_prod (Finset.range N) (fun k => (q k)⁻¹)
    (fun k _ => inv_ne_zero (ne_of_gt (hq k)))]
  simp only [Real.log_inv, Finset.sum_neg_distrib]
  rfl

/-- Even log(u) <= u is sufficient to transfer qualitative divergence. -/
theorem logMean_le_arithmeticMean
    (q : ℕ → ℝ) (hq : ∀ k, 0 < q k) (N : ℕ) :
    logReciprocalMean q N ≤ reciprocalMean q N := by
  have hp : ∀ k, -Real.log (q k) ≤ (q k)⁻¹ := by
    intro k
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (hq k))
    rw [Real.log_inv] at h
    linarith
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hp k)
  rw [Finset.sum_neg_distrib] at hs
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)

/-- Conditional qualitative reciprocal-growth theorem for arbitrary finite hierarchy
    height. The NORMALIZED HIERARCHY IS AN EXPLICIT HYPOTHESIS. -/
theorem hierarchy_reciprocal_growth
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C) (hδ : UpperNull δ) :
    Tendsto (reciprocalGeometricMean q) atTop atTop ∧
    Tendsto (reciprocalMean q) atTop atTop := by
  have hlog := tail_potentials_force_log_growth q C H.q_pos H.C_pos
    (hierarchy_tail_potentials H hδ)
  constructor
  · have he := Real.tendsto_exp_atTop.comp hlog
    have hid : reciprocalGeometricMean q = fun N => Real.exp (logReciprocalMean q N) := by
      funext N
      exact geometricMean_eq_exp_logMean q H.q_pos N
    rw [hid]
    exact he
  · rw [Filter.tendsto_atTop_atTop] at hlog ⊢
    intro target
    obtain ⟨N, hN⟩ := hlog target
    exact ⟨N, fun k hk => le_trans (hN k hk) (logMean_le_arithmeticMean q H.q_pos k)⟩

end BfgsVerification.ReciprocalGrowth
