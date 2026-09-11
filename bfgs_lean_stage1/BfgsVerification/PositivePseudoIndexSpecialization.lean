import BfgsVerification.PositivePseudoIndex

noncomputable section
open Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {R : Type*} [CommRing R]

theorem positive_pseudo_index_specialize {p q Q r : Polynomial R} {k : ℕ}
    (he : (C q.leadingCoeff)^(2*k)*p=q*Q+r) (f : R →+* ℝ)
    (hf : f q.leadingCoeff ≠ 0) :
    rationalCauchyIndex (p.map f) (q.map f) =
      if r.map f=0 then 0
      else infinityVariation (r.map f) (q.map f)-rationalCauchyIndex (q.map f) (r.map f) := by
  classical
  have hq : q.map f ≠ 0 := by
    intro hz
    have hc := congrArg (fun s : Polynomial ℝ => s.coeff q.natDegree) hz
    simp only [coeff_map, coeff_natDegree, coeff_zero] at hc
    exact hf hc
  have hc : 0 < (f q.leadingCoeff)^(2*k) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hf) k
  have hm : C ((f q.leadingCoeff)^(2*k))*p.map f=q.map f*Q.map f+r.map f := by
    have h := congrArg (Polynomial.map f) he
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_add] at h
    rw [← Polynomial.C_pow] at h
    exact h
  by_cases hr : r.map f=0
  · rw [if_pos hr]
    exact positive_pseudo_index_zero hc hm hq hr
  · rw [if_neg hr]
    exact positive_pseudo_index_recurrence hc hm hq hr

end RealAlgebraicGeometry

open RealAlgebraicGeometry

def PositivePseudoIndexSpecializationTarget : Prop := ∀ {n : ℕ}
    (p q Q r : Polynomial (MvPolynomial (Fin n) ℝ)) (k : ℕ),
    (C q.leadingCoeff)^(2*k)*p=q*Q+r → ∀ x : Fin n → ℝ,
    MvPolynomial.eval x q.leadingCoeff≠0 →
      rationalCauchyIndex (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x)) =
        if r.map (MvPolynomial.eval x)=0 then 0 else
          infinityVariation (r.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x)) -
            rationalCauchyIndex (q.map (MvPolynomial.eval x)) (r.map (MvPolynomial.eval x))

theorem positivePseudoIndexSpecialization : PositivePseudoIndexSpecializationTarget := by
  intro n p q Q r k he x hx
  exact positive_pseudo_index_specialize he (MvPolynomial.eval x) hx

end BfgsVerification
