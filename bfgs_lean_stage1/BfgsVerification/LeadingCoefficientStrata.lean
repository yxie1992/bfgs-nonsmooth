import BfgsVerification.PositivePseudoSpecialization
import BfgsVerification.SemialgebraicGraphs
import Mathlib.Algebra.Polynomial.EraseLead

/-! The exceptional zero-leading-coefficient branch preserves the actual
specialized polynomial and strictly lowers its symbolic degree. -/
noncomputable section
open Polynomial Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {R S : Type*} [CommRing R] [CommRing S]

theorem eraseLead_map_of_leadingCoeff_zero (p : Polynomial R) (f : R →+* S)
    (hf : f p.leadingCoeff=0) : p.eraseLead.map f=p.map f := by
  apply Polynomial.ext
  intro i
  simp only [coeff_map,eraseLead_coeff]
  split_ifs with hi
  · subst i
    simp [coeff_natDegree,hf]
  · rfl

theorem eraseLead_branch_degree (p : Polynomial R) (hp : p≠0) :
    p.eraseLead.degree<p.degree := Polynomial.degree_eraseLead_lt hp

theorem leadingCoeff_zero_semialgebraic {σ : Type*} [Finite σ]
    (q : Polynomial (MvPolynomial σ ℝ)) :
    RealAlgebraicGeometry.IsSemialgebraic {x : σ → ℝ | MvPolynomial.eval x q.leadingCoeff=0} :=
  isSemialgebraic_equal_zero q.leadingCoeff

theorem leadingCoeff_nonzero_semialgebraic {σ : Type*} [Finite σ]
    (q : Polynomial (MvPolynomial σ ℝ)) :
    RealAlgebraicGeometry.IsSemialgebraic {x : σ → ℝ | MvPolynomial.eval x q.leadingCoeff≠0} :=
  (isSemialgebraic_equal_zero q.leadingCoeff).compl

end RealAlgebraicGeometry
end BfgsVerification
