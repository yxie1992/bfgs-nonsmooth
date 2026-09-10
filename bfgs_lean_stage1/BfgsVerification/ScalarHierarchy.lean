import Mathlib

/-!
# A finite nonnegative hierarchy gives a weighted scalar recurrence

STATUS: uncompiled draft proof scripts.

This file is deliberately independent of matrices. Its inputs are the normalized
inequalities to be derived from the actual principal-minor theorem. A successful
build of this file alone would NOT prove the principal-minor theorem.

Index convention: `e 1` is the trace slot; `e (n+1) = 0` is the terminal slot.
-/

noncomputable section
open scoped BigOperators

namespace BfgsVerification.ScalarHierarchy

def weightedPotential (n : ℕ) (r : ℝ) (e : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, r ^ j * e (j + 1)

def shiftedPotential (n : ℕ) (r : ℝ) (e : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, r ^ j * e (j + 2)

@[simp] theorem weighted_succ (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    weightedPotential (n + 1) r e =
      weightedPotential n r e + r ^ n * e (n + 1) := by
  simp only [weightedPotential, Finset.sum_range_succ]

@[simp] theorem shifted_succ (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    shiftedPotential (n + 1) r e =
      shiftedPotential n r e + r ^ n * e (n + 2) := by
  simp only [shiftedPotential, Finset.sum_range_succ]

/-- The finite shift identity, including its upper-boundary term. -/
theorem shift_identity (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    r * shiftedPotential n r e + e 1 =
      weightedPotential n r e + r ^ n * e (n + 1) := by
  induction n with
  | zero => simp [weightedPotential, shiftedPotential]
  | succ n ih =>
      rw [weighted_succ, shifted_succ, pow_succ]
      have hindex : n + 1 + 1 = n + 2 := by omega
      rw [hindex]
      nlinarith [ih]

theorem weighted_nonneg (n : ℕ) (r : ℝ) (e : ℕ → ℝ)
    (hr : 0 ≤ r) (he : ∀ j, 0 ≤ e j) :
    0 ≤ weightedPotential n r e := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hr j) (he (j + 1)))

theorem first_le_weighted (n : ℕ) (r : ℝ) (e : ℕ → ℝ)
    (hn : 0 < n) (hr : 0 ≤ r) (he : ∀ j, 0 ≤ e j) :
    e 1 ≤ weightedPotential n r e := by
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have h := Finset.single_le_sum
    (f := fun j : ℕ => r ^ j * e (j + 1))
    (s := Finset.range n)
    (fun j _ => mul_nonneg (pow_nonneg hr j) (he (j + 1))) hmem
  simpa only [pow_zero, zero_add, one_mul] using h

/-- The weighted recurrence used in M.2 and M.3, in cross-multiplied form. -/
theorem weighted_step
    (n : ℕ) (e eNext : ℕ → ℝ) (q K η δ : ℝ)
    (hK : 0 ≤ K) (hη : 0 < η)
    (he : ∀ j, 0 ≤ e j) (hterminal : e (n + 1) = 0)
    (hstep : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      q * eNext j ≤ K * e (j + 1) + δ * e j) :
    q * weightedPotential n (K / η) eNext ≤
      (η + δ) * weightedPotential n (K / η) e := by
  let r : ℝ := K / η
  have hr : 0 ≤ r := div_nonneg hK hη.le
  have hcoeff : η * r = K := by
    dsimp [r]
    field_simp [ne_of_gt hη]
  have hshift := shift_identity n r e
  rw [hterminal, mul_zero, add_zero] at hshift
  have hshift_bound : K * shiftedPotential n r e ≤ η * weightedPotential n r e := by
    calc
      K * shiftedPotential n r e = η * (r * shiftedPotential n r e) := by
        rw [← hcoeff]
        ring
      _ ≤ η * weightedPotential n r e :=
        mul_le_mul_of_nonneg_left (by linarith [he 1]) hη.le
  change q * weightedPotential n r eNext ≤ (η + δ) * weightedPotential n r e
  calc
    q * weightedPotential n r eNext =
        ∑ j ∈ Finset.range n, r ^ j * (q * eNext (j + 1)) := by
      unfold weightedPotential
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j ∈ Finset.range n,
        r ^ j * (K * e (j + 2) + δ * e (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have h := hstep (j + 1) (by omega) (by omega)
      have hindex : j + 1 + 1 = j + 2 := by omega
      rw [hindex] at h
      exact mul_le_mul_of_nonneg_left h (pow_nonneg hr j)
    _ = K * shiftedPotential n r e + δ * weightedPotential n r e := by
      unfold shiftedPotential weightedPotential
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (η + δ) * weightedPotential n r e := by
      nlinarith [hshift_bound]

/-- This is an INTERFACE to the matrix proof, not a proof of that interface. -/
structure NormalizedHierarchy (n : ℕ) (E : ℕ → ℕ → ℝ)
    (q δ : ℕ → ℝ) (K C : ℝ) : Prop where
  dimension_pos : 0 < n
  q_pos : ∀ k, 0 < q k
  K_nonneg : 0 ≤ K
  C_pos : 0 < C
  coefficient_nonneg : ∀ k j, 0 ≤ E k j
  trace_pos : ∀ k, 0 < E k 1
  terminal : ∀ k, E k (n + 1) = 0
  trace_bound : ∀ k, q k ≤ C * E k 1
  step : ∀ k j, 1 ≤ j → j ≤ n →
    q k * E (k + 1) j ≤ K * E k (j + 1) + δ k * E k j

/-- This is an epsilon-tail formulation, not an assumed growth conclusion. -/
def UpperNull (δ : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ k : ℕ, J ≤ k → δ k ≤ ε

/-- For each positive contraction factor, construct one fixed weighted potential
    and one tail. The potential does not vary with the index along that tail. -/
theorem hierarchy_tail_potentials
    {n : ℕ} {E : ℕ → ℕ → ℝ} {q δ : ℕ → ℝ} {K C : ℝ}
    (H : NormalizedHierarchy n E q δ K C) (hδ : UpperNull δ) :
    ∀ A : ℝ, 0 < A →
      ∃ J : ℕ, ∃ V : ℕ → ℝ,
        (∀ k, 0 < V k) ∧
        (∀ k, J ≤ k → q k * V (k + 1) ≤ A * V k) ∧
        (∀ k, q k ≤ C * V k) := by
  intro A hA
  let η : ℝ := A / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨J, hJ⟩ := hδ η hη
  let V : ℕ → ℝ := fun k => weightedPotential n (K / η) (E k)
  have hdom : ∀ k, E k 1 ≤ V k := by
    intro k
    exact first_le_weighted n (K / η) (E k) H.dimension_pos
      (div_nonneg H.K_nonneg hη.le) (H.coefficient_nonneg k)
  refine ⟨J, V, ?_, ?_, ?_⟩
  · intro k
    exact lt_of_lt_of_le (H.trace_pos k) (hdom k)
  · intro k hk
    have hrec := weighted_step n (E k) (E (k + 1)) (q k) K η (δ k)
      H.K_nonneg hη (H.coefficient_nonneg k) (H.terminal k) (H.step k)
    have hfactor : η + δ k ≤ A := by
      have hdk := hJ k hk
      dsimp [η] at *
      linarith
    have hV : 0 ≤ V k := (lt_of_lt_of_le (H.trace_pos k) (hdom k)).le
    exact le_trans hrec (mul_le_mul_of_nonneg_right hfactor hV)
  · intro k
    exact le_trans (H.trace_bound k)
      (mul_le_mul_of_nonneg_left (hdom k) H.C_pos.le)

end BfgsVerification.ScalarHierarchy
