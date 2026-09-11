import BfgsVerification.SemialgebraicQuadraticProjection
import BfgsVerification.PolynomialFibers
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Every actual multivariate polynomial of degree at most two in the
eliminated coordinate reduces to its actual three coefficient polynomials. -/
noncomputable section
open scoped BigOperators
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem degree_two_parameterEval (p : MvPolynomial (Option (Fin n)) ℝ)
    (hd : p.degreeOf none ≤ 2) (x : Vec n) (t : ℝ) :
    parameterEval p (x,t) = quadraticValue
      (MvPolynomial.eval x ((MvPolynomial.optionEquivLeft ℝ (Fin n) p).coeff 2))
      (MvPolynomial.eval x ((MvPolynomial.optionEquivLeft ℝ (Fin n) p).coeff 1))
      (MvPolynomial.eval x ((MvPolynomial.optionEquivLeft ℝ (Fin n) p).coeff 0)) t := by
  let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hdeg : (Q.map (MvPolynomial.eval x)).natDegree < 3 :=
    Polynomial.natDegree_map_le.trans_lt
      ((MvPolynomial.natDegree_optionEquivLeft ℝ (Fin n) p).le.trans_lt (by omega))
  have heval : parameterEval p (x,t)=(Q.map (MvPolynomial.eval x)).eval t := by
    have hg : (fun i : Option (Fin n) => Option.elim i t x) = parameterPoint x t := by
      funext i
      cases i <;> rfl
    change MvPolynomial.eval (parameterPoint x t) p = _
    rw [← hg]
    exact MvPolynomial.optionEquivLeft_elim_eval ℝ (Fin n) x t p
  rw [heval,Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Polynomial.coeff_map,pow_zero,
    mul_one,zero_add,pow_one]
  unfold quadraticValue
  change _ = MvPolynomial.eval x (Q.coeff 2)*t^2+
    MvPolynomial.eval x (Q.coeff 1)*t+MvPolynomial.eval x (Q.coeff 0)
  ring

theorem degree_two_projections_semialgebraic (p : MvPolynomial (Option (Fin n)) ℝ)
    (hd : p.degreeOf none ≤ 2) :
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, parameterEval p (x,t)=0} ∧
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, 0<parameterEval p (x,t)} ∧
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, 0≤parameterEval p (x,t)} := by
  let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hzero := quadratic_zero_projection_semialgebraic (Q.coeff 2) (Q.coeff 1) (Q.coeff 0)
  have hpos := quadratic_positive_projection_semialgebraic (Q.coeff 2) (Q.coeff 1) (Q.coeff 0)
  have hnonneg := quadratic_nonnegative_projection_semialgebraic (Q.coeff 2) (Q.coeff 1) (Q.coeff 0)
  constructor
  · convert hzero using 1
    ext x
    simp only [mem_setOf_eq,degree_two_parameterEval p hd]
    rfl
  · constructor
    · convert hpos using 1
      ext x
      simp only [mem_setOf_eq,degree_two_parameterEval p hd]
      rfl
    · convert hnonneg using 1
      ext x
      simp only [mem_setOf_eq,degree_two_parameterEval p hd]
      rfl

end RealAlgebraicGeometry
end BfgsVerification
