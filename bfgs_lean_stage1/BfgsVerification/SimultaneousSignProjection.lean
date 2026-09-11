import BfgsVerification.ParameterSignQueries
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Global scalar existential elimination for one simultaneous sign pattern
of an arbitrary finite polynomial family. There are no degree, root
multiplicity, or generic-parameter hypotheses. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Finite σ] {m : ℕ}

theorem real_sign_pattern_semialgebraic
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) (ω : Fin m → SignType) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, SignType.sign (((q i).map (MvPolynomial.eval x)).eval t) = ω i} := by
  have hP := (finiteSemialgebraic_product_signQueryExpression q ω).predicate (0 < ·)
  have hD := (finiteSemialgebraic_derivative_signQueryExpression q ω).predicate (0 < ·)
  have hL := isSemialgebraic_forall_finite
    (fun i : Fin m => {x : σ → ℝ |
      (-1 : SignType)^((q i).map (MvPolynomial.eval x)).natDegree *
        SignType.sign ((q i).map (MvPolynomial.eval x)).leadingCoeff = ω i})
    (fun i => ((finiteSemialgebraic_degree_leadingSign (q i)).map
      (fun ds : ℕ × SignType => (-1 : SignType)^ds.1 * ds.2)).fiber (ω i))
  have hR := isSemialgebraic_forall_finite
    (fun i : Fin m => {x : σ → ℝ |
      SignType.sign ((q i).map (MvPolynomial.eval x)).leadingCoeff = ω i})
    (fun i => (finiteSemialgebraic_leadingSign (q i)).fiber (ω i))
  convert hP.union (hD.union (hL.union hR)) using 1
  ext x
  exact exists_real_sign_pattern_iff_queries_and_tails
    (fun i => (q i).map (MvPolynomial.eval x)) ω

theorem polynomial_simultaneous_sign_projection
    (q : Fin m → MvPolynomial (Option σ) ℝ) (ω : Fin m → SignType) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, SignType.sign (MvPolynomial.eval (fun j => Option.elim j t x) (q i)) = ω i} := by
  have h := real_sign_pattern_semialgebraic
    (fun i => MvPolynomial.optionEquivLeft ℝ σ (q i)) ω
  convert h using 1
  ext x
  apply exists_congr
  intro t
  apply forall_congr'
  intro i
  rw [← MvPolynomial.optionEquivLeft_elim_eval ℝ σ x t (q i)]

end RealAlgebraicGeometry
end BfgsVerification
