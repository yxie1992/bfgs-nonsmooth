import BfgsVerification.ConnectedNonzeroSign
import BfgsVerification.PolynomialFiberDegree

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n m : ℕ}

def zeroFiberPattern (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) : Set (Vec n) :=
  {x | ∀ i, i ∈ Z ↔ fiberPolynomial (P i) x = 0}

def survivingPolynomialProduct (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) : MvPolynomial (Option (Fin n)) ℝ :=
  ∏ i ∈ Finset.univ \ Z, P i

theorem zeroFiberPattern_semialgebraic (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) : IsSemialgebraic (zeroFiberPattern P Z) := by
  apply isSemialgebraic_forall_finite
  intro i
  by_cases hi : i ∈ Z
  · simpa only [hi,true_iff] using fiberPolynomial_zero_semialgebraic (P i)
  · simpa only [hi,false_iff,mem_compl_iff,mem_setOf_eq] using
      (fiberPolynomial_zero_semialgebraic (P i)).compl

theorem zeroFiberPatterns_cover (P : Fin m → MvPolynomial (Option (Fin n)) ℝ) :
    (⋃ Z : Finset (Fin m), zeroFiberPattern P Z) = univ := by
  classical
  ext x
  simp only [mem_univ,iff_true,mem_iUnion]
  refine ⟨Finset.univ.filter (fun i => fiberPolynomial (P i) x = 0),?_⟩
  intro i
  simp

theorem fiberPolynomial_survivingProduct (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) (x : Vec n) :
    fiberPolynomial (survivingPolynomialProduct P Z) x =
      ∏ i ∈ Finset.univ \ Z, fiberPolynomial (P i) x := by
  simp only [survivingPolynomialProduct,fiberPolynomial,map_prod]

theorem survivingProduct_fiber_nonzero (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) {x : Vec n} (hx : x ∈ zeroFiberPattern P Z) :
    fiberPolynomial (survivingPolynomialProduct P Z) x ≠ 0 := by
  rw [fiberPolynomial_survivingProduct]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact fun he => (Finset.mem_sdiff.mp hi).2 ((hx i).mpr he)

theorem survivingProduct_eval_zero_of_factor (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) (x : Vec n) (t : ℝ) (i : Fin m) (hi : i ∉ Z)
    (hz : (fiberPolynomial (P i) x).eval t = 0) :
    (fiberPolynomial (survivingPolynomialProduct P Z) x).eval t = 0 := by
  classical
  rw [fiberPolynomial_survivingProduct,Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hi⟩) hz

theorem factor_nonzero_off_surviving_root (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) (x : Vec n) (t : ℝ) (i : Fin m) (hi : i ∉ Z)
    (hz : (fiberPolynomial (survivingPolynomialProduct P Z) x).eval t ≠ 0) :
    (fiberPolynomial (P i) x).eval t ≠ 0 :=
  fun he => hz (survivingProduct_eval_zero_of_factor P Z x t i hi he)

theorem zero_pattern_factor_eval_zero (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (Z : Finset (Fin m)) {x : Vec n} (hx : x ∈ zeroFiberPattern P Z)
    (t : ℝ) (i : Fin m) (hi : i ∈ Z) : (fiberPolynomial (P i) x).eval t = 0 := by
  rw [(hx i).mp hi,Polynomial.eval_zero]

end RealAlgebraicGeometry
end BfgsVerification
