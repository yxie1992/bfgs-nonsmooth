import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact elimination of one real variable from a finite system of strict or
weak affine inequalities. Coefficients are arbitrary real values, including
zero; no feasibility or nonempty constraint family is assumed. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- A finite weak lower/upper system has a common point, also when one or both
sets of bounds are empty. -/
theorem exists_between_finite_weak (lo hi : Finset ℝ)
    (h : ∀ x ∈ lo, ∀ y ∈ hi, x ≤ y) :
    ∃ t : ℝ, (∀ x ∈ lo, x ≤ t) ∧ ∀ y ∈ hi, t ≤ y := by
  by_cases hlo : lo.Nonempty
  · refine ⟨lo.max' hlo, fun x hx => Finset.le_max' lo x hx, ?_⟩
    intro y hy
    exact h _ (Finset.max'_mem lo hlo) y hy
  · by_cases hhi : hi.Nonempty
    · refine ⟨hi.min' hhi, ?_, fun y hy => Finset.min'_le hi y hy⟩
      intro x hx
      exact (hlo ⟨x,hx⟩).elim
    · exact ⟨0, fun x hx => (hlo ⟨x,hx⟩).elim,
        fun y hy => (hhi ⟨y,hy⟩).elim⟩

/-- Division-free one-variable Fourier--Motzkin criterion for strict
inequalities. The two signs in each pair are ordered explicitly. -/
theorem exists_strict_affine_iff {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, a i * t < b i) ↔
      (∀ i, a i = 0 → 0 < b i) ∧
      ∀ i j, a i < 0 → 0 < a j → b j * a i < b i * a j := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa only [hi,zero_mul] using ht i, ?_⟩
    intro i j hi hj
    have hi' := mul_lt_mul_of_pos_right (ht i) hj
    have hj' := mul_lt_mul_of_neg_right (ht j) hi
    nlinarith
  · rintro ⟨hzero,hpair⟩
    let lo : Finset ℝ := (Finset.univ.filter (fun i => a i < 0)).image (fun i => b i / a i)
    let hi : Finset ℝ := (Finset.univ.filter (fun i => 0 < a i)).image (fun i => b i / a i)
    have hsep : ∀ x ∈ lo, ∀ y ∈ hi, x < y := by
      intro x hx y hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
      have hi0 := (Finset.mem_filter.mp hi).2
      have hj0 := (Finset.mem_filter.mp hj).2
      have h := hpair i j hi0 hj0
      apply (div_lt_iff_of_neg hi0).mpr
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hj0).mpr h
    obtain ⟨t,htlo,hthi⟩ := Order.exists_between_finsets lo hi hsep
    refine ⟨t,fun i => ?_⟩
    rcases lt_trichotomy (a i) 0 with hn | hz | hp
    · have hb : b i / a i < t := htlo _
        (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩)
      simpa only [mul_comm] using (div_lt_iff_of_neg hn).mp hb
    · simpa only [hz,zero_mul] using hzero i hz
    · have hb : t < b i / a i := hthi _
        (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩)
      simpa only [mul_comm] using (lt_div_iff₀ hp).mp hb

/-- The weak variant includes feasible touching lower and upper bounds. -/
theorem exists_weak_affine_iff {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, a i * t ≤ b i) ↔
      (∀ i, a i = 0 → 0 ≤ b i) ∧
      ∀ i j, a i < 0 → 0 < a j → b j * a i ≤ b i * a j := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa only [hi,zero_mul] using ht i, ?_⟩
    intro i j hi hj
    have hi' := mul_le_mul_of_nonneg_right (ht i) hj.le
    have hj' := mul_le_mul_of_nonpos_right (ht j) hi.le
    nlinarith
  · rintro ⟨hzero,hpair⟩
    let lo : Finset ℝ := (Finset.univ.filter (fun i => a i < 0)).image (fun i => b i / a i)
    let hi : Finset ℝ := (Finset.univ.filter (fun i => 0 < a i)).image (fun i => b i / a i)
    have hsep : ∀ x ∈ lo, ∀ y ∈ hi, x ≤ y := by
      intro x hx y hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
      have hi0 := (Finset.mem_filter.mp hi).2
      have hj0 := (Finset.mem_filter.mp hj).2
      have h := hpair i j hi0 hj0
      apply (div_le_iff_of_neg hi0).mpr
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hj0).mpr h
    obtain ⟨t,htlo,hthi⟩ := exists_between_finite_weak lo hi hsep
    refine ⟨t,fun i => ?_⟩
    rcases lt_trichotomy (a i) 0 with hn | hz | hp
    · have hb : b i / a i ≤ t := htlo _
        (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩)
      simpa only [mul_comm] using (div_le_iff_of_neg hn).mp hb
    · simpa only [hz,zero_mul] using hzero i hz
    · have hb : t ≤ b i / a i := hthi _
        (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩)
      simpa only [mul_comm] using (le_div_iff₀ hp).mp hb

end RealAlgebraicGeometry
end BfgsVerification
