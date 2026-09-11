import BfgsVerification.PolynomialFiberDegree
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Iterated differentiation commutes with actual polynomial specialization.
The derivative polynomials therefore give genuine algebraic root-order tests. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem fiberPolynomial_pderiv (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) :
    fiberPolynomial (MvPolynomial.pderiv none p) x = (fiberPolynomial p x).derivative := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [fiberPolynomial]
  | add p q hp hq => simp [fiberPolynomial] at hp hq ⊢; rw [hp,hq]
  | mul_X p i hp =>
    cases i with
    | none =>
      simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_self,fiberPolynomial,
        map_add,map_mul,map_one,MvPolynomial.eval₂Hom_X,Polynomial.derivative_mul,
        Polynomial.derivative_X,mul_one] at hp ⊢
      rw [hp]
      simp
    | some i =>
      simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_of_ne (Option.some_ne_none i),
        mul_zero,add_zero,fiberPolynomial,map_mul,MvPolynomial.eval₂Hom_X,
        Polynomial.derivative_mul,Polynomial.derivative_C,mul_zero,add_zero] at hp ⊢
      rw [hp]
      simp

def verticalDerivative (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    MvPolynomial (Option (Fin n)) ℝ := (MvPolynomial.pderiv none)^[k] p

theorem fiberPolynomial_verticalDerivative (p : MvPolynomial (Option (Fin n)) ℝ)
    (x : Vec n) (k : ℕ) :
    fiberPolynomial (verticalDerivative p k) x = Polynomial.derivative^[k] (fiberPolynomial p x) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    simp only [verticalDerivative,Function.iterate_succ_apply'] at hk ⊢
    rw [fiberPolynomial_pderiv,hk]

theorem verticalDerivative_eval (p : MvPolynomial (Option (Fin n)) ℝ)
    (v : Option (Fin n) → ℝ) (k : ℕ) :
    MvPolynomial.eval v (verticalDerivative p k) =
      (Polynomial.derivative^[k] (fiberPolynomial p (fun i => v (some i)))).eval (v none) := by
  rw [← fiberPolynomial_verticalDerivative,fiberPolynomial_eval]
  change MvPolynomial.eval v _ = MvPolynomial.eval (parameterPoint (fun i => v (some i)) (v none)) _
  have hv : parameterPoint (fun i => v (some i)) (v none) = v := by
    funext i
    cases i <;> rfl
  rw [hv]

end RealAlgebraicGeometry
end BfgsVerification
