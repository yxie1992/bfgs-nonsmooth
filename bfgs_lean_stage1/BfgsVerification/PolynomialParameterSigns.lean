import BfgsVerification.FiniteSemialgebraicFunctions
import BfgsVerification.LeadingCoefficientStrata
import BfgsVerification.PositivePseudoIndex

/-! The actual degree and leading-coefficient sign of each specialization have
finite quantifier-free semialgebraic fibers, including every degree drop. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Finite σ]

theorem finiteSemialgebraic_degree_leadingSign
    (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      ((p.map (MvPolynomial.eval x)).natDegree,
        SignType.sign (p.map (MvPolynomial.eval x)).leadingCoeff)) := by
  classical
  suffices H : ∀ d : ℕ, ∀ p : Polynomial (MvPolynomial σ ℝ), p.natDegree = d →
      FiniteSemialgebraicFunction (fun x : σ → ℝ =>
        ((p.map (MvPolynomial.eval x)).natDegree,
          SignType.sign (p.map (MvPolynomial.eval x)).leadingCoeff)) from H _ p rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hd
    by_cases hp : p = 0
    · simpa [hp] using (FiniteSemialgebraicFunction.const (σ := σ) (0, (0 : SignType)))
    have he : FiniteSemialgebraicFunction (fun x : σ → ℝ =>
        ((p.eraseLead.map (MvPolynomial.eval x)).natDegree,
          SignType.sign (p.eraseLead.map (MvPolynomial.eval x)).leadingCoeff)) := by
      rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hz
      · exact ih _ (hlt.trans_eq hd) _ rfl
      · simpa [hz] using (FiniteSemialgebraicFunction.const (σ := σ) (0, (0 : SignType)))
    have hs := (finiteSemialgebraic_polynomial_sign p.leadingCoeff).map
      (fun s => (p.natDegree, s))
    have hb := he.ite hs (leadingCoeff_zero_semialgebraic p)
    convert hb using 1
    funext x
    by_cases hx : MvPolynomial.eval x p.leadingCoeff = 0
    · simp only [mem_setOf_eq, if_pos hx, eraseLead_map_of_leadingCoeff_zero p _ hx]
    · simp only [mem_setOf_eq, if_neg hx,
        natDegree_map_of_leadingCoeff_ne_zero _ hx,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ hx]

theorem finiteSemialgebraic_polynomial_degree (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      (p.map (MvPolynomial.eval x)).natDegree) :=
  (finiteSemialgebraic_degree_leadingSign p).map Prod.fst

theorem finiteSemialgebraic_leadingSign (p : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      SignType.sign (p.map (MvPolynomial.eval x)).leadingCoeff) :=
  (finiteSemialgebraic_degree_leadingSign p).map Prod.snd

theorem polynomial_map_zero_semialgebraic (p : Polynomial (MvPolynomial σ ℝ)) :
    IsSemialgebraic {x : σ → ℝ | p.map (MvPolynomial.eval x) = 0} := by
  simpa only [sign_eq_zero_iff, leadingCoeff_eq_zero] using
    (finiteSemialgebraic_leadingSign p).fiber 0

theorem finiteSemialgebraic_infinityVariation
    (p q : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      infinityVariation (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))) := by
  have h := (finiteSemialgebraic_degree_leadingSign (p*q)).map
    (fun ds : ℕ × SignType => if Odd ds.1 then (ds.2 : ℤ) else 0)
  simpa only [Polynomial.map_mul, infinityVariation_eq_odd] using h

end RealAlgebraicGeometry
end BfgsVerification
