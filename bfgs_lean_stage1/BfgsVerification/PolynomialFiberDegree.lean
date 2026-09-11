import BfgsVerification.PolynomialFibers
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Actual coefficient specialization and degree strata, including fibers
which vanish identically. The degree bound is uniform in all parameters. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

def fiberCoefficient (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    MvPolynomial (Fin n) ℝ := (MvPolynomial.optionEquivLeft ℝ (Fin n) p).coeff k

theorem fiberPolynomial_eq_map (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) :
    fiberPolynomial p x = (MvPolynomial.optionEquivLeft ℝ (Fin n) p).map
      (MvPolynomial.eval x) := by
  apply Polynomial.funext
  intro t
  rw [fiberPolynomial_eval]
  have hg : (fun i : Option (Fin n) => Option.elim i t x) = parameterPoint x t := by
    funext i
    cases i <;> rfl
  change MvPolynomial.eval (parameterPoint x t) p = _
  rw [← hg]
  exact MvPolynomial.optionEquivLeft_elim_eval ℝ (Fin n) x t p

theorem fiberPolynomial_coeff (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) (k : ℕ) :
    (fiberPolynomial p x).coeff k = MvPolynomial.eval x (fiberCoefficient p k) := by
  simp [fiberPolynomial_eq_map,fiberCoefficient]

theorem fiberPolynomial_natDegree_le (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) :
    (fiberPolynomial p x).natDegree ≤ p.degreeOf none := by
  rw [fiberPolynomial_eq_map]
  exact Polynomial.natDegree_map_le.trans (MvPolynomial.natDegree_optionEquivLeft ℝ (Fin n) p).le

theorem fiberPolynomial_zero_iff (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) :
    fiberPolynomial p x = 0 ↔
      ∀ k ∈ Finset.range (p.degreeOf none + 1), MvPolynomial.eval x (fiberCoefficient p k) = 0 := by
  constructor
  · intro h k _
    rw [← fiberPolynomial_coeff,h,Polynomial.coeff_zero]
  · intro h
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < p.degreeOf none + 1
    · rw [fiberPolynomial_coeff]
      exact h k (Finset.mem_range.mpr hk)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((fiberPolynomial_natDegree_le p x).trans_lt (by omega))

theorem fiberPolynomial_zero_semialgebraic (p : MvPolynomial (Option (Fin n)) ℝ) :
    IsSemialgebraic {x : Vec n | fiberPolynomial p x = 0} := by
  have h := isSemialgebraic_finset_inter (Finset.range (p.degreeOf none + 1))
    (fun k => {x : Vec n | MvPolynomial.eval x (fiberCoefficient p k) = 0})
    (fun k _ => isSemialgebraic_equal_zero _)
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_iInter,fiberPolynomial_zero_iff]

theorem fiberPolynomial_degree_iff (p : MvPolynomial (Option (Fin n)) ℝ)
    (x : Vec n) (k : ℕ) :
    (fiberPolynomial p x ≠ 0 ∧ (fiberPolynomial p x).natDegree = k) ↔
      MvPolynomial.eval x (fiberCoefficient p k) ≠ 0 ∧
      ∀ j ∈ (Finset.range (p.degreeOf none + 1)).filter (k < ·),
        MvPolynomial.eval x (fiberCoefficient p j) = 0 := by
  constructor
  · rintro ⟨hne,hk⟩
    constructor
    · rw [← fiberPolynomial_coeff,← hk]
      exact Polynomial.leadingCoeff_ne_zero.mpr hne
    · intro j hj
      rw [← fiberPolynomial_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hk ▸ (Finset.mem_filter.mp hj).2)
  · rintro ⟨hk,h⟩
    rw [← fiberPolynomial_coeff] at hk
    have hle : (fiberPolynomial p x).natDegree ≤ k := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj
      by_cases hd : j < p.degreeOf none + 1
      · rw [fiberPolynomial_coeff]
        exact h j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd,hj⟩)
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt
          ((fiberPolynomial_natDegree_le p x).trans_lt (by omega))
    exact ⟨fun he => hk (by rw [he,Polynomial.coeff_zero]),
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hk⟩

theorem fiberPolynomial_degree_semialgebraic (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    IsSemialgebraic {x : Vec n | fiberPolynomial p x ≠ 0 ∧ (fiberPolynomial p x).natDegree = k} := by
  have h := (isSemialgebraic_equal_zero (fiberCoefficient p k)).compl.inter
    (isSemialgebraic_finset_inter ((Finset.range (p.degreeOf none + 1)).filter (k < ·))
      (fun j => {x : Vec n | MvPolynomial.eval x (fiberCoefficient p j) = 0})
      (fun j _ => isSemialgebraic_equal_zero _))
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_inter_iff,mem_compl_iff,mem_iInter,fiberPolynomial_degree_iff]

theorem fiberPolynomial_degree_partition (p : MvPolynomial (Option (Fin n)) ℝ) :
    {x : Vec n | fiberPolynomial p x = 0} ∪
      (⋃ k ∈ Finset.range (p.degreeOf none + 1),
        {x : Vec n | fiberPolynomial p x ≠ 0 ∧ (fiberPolynomial p x).natDegree = k}) = univ := by
  ext x
  simp only [mem_union,mem_setOf_eq,mem_iUnion,mem_univ,iff_true]
  by_cases h : fiberPolynomial p x = 0
  · exact Or.inl h
  · exact Or.inr ⟨(fiberPolynomial p x).natDegree,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (fiberPolynomial_natDegree_le p x)),h,rfl⟩

end RealAlgebraicGeometry
end BfgsVerification
