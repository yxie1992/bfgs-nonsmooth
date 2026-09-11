import BfgsVerification.PolynomialParameterSigns

/-! Parameter-uniform fibers of the actual rational Cauchy index and actual
root Tarski queries. The finite recursion is proved from positive symbolic
pseudo-division and strict denominator-degree decrease. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Finite σ]

theorem positive_pseudo_index_recurrence_total {p q Q r : Polynomial ℝ} {c : ℝ}
    (hc : 0 < c) (he : C c * p = q * Q + r) (hq : q ≠ 0) :
    rationalCauchyIndex p q = infinityVariation r q - rationalCauchyIndex q r := by
  by_cases hr : r = 0
  · rw [positive_pseudo_index_zero hc he hq hr, hr,
      rationalCauchyIndex_zero_denominator, infinityVariation_eq_odd]
    simp
  · exact positive_pseudo_index_recurrence hc he hq hr

theorem finiteSemialgebraic_rationalCauchyIndex
    (p q : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      rationalCauchyIndex (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))) := by
  classical
  suffices H : ∀ d : ℕ, ∀ q : Polynomial (MvPolynomial σ ℝ), q.natDegree = d →
      ∀ p : Polynomial (MvPolynomial σ ℝ),
      FiniteSemialgebraicFunction (fun x : σ → ℝ =>
        rationalCauchyIndex (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))) from
    H _ q rfl p
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro q hd p
    by_cases hq : q = 0
    · simpa [hq, rationalCauchyIndex_zero_denominator] using
        (FiniteSemialgebraicFunction.const (σ := σ) (0 : ℤ))
    have herase : FiniteSemialgebraicFunction (fun x : σ → ℝ =>
        rationalCauchyIndex (p.map (MvPolynomial.eval x))
          (q.eraseLead.map (MvPolynomial.eval x))) := by
      rcases q.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hz
      · exact ih _ (hlt.trans_eq hd) _ rfl p
      · simpa [hz, rationalCauchyIndex_zero_denominator] using
          (FiniteSemialgebraicFunction.const (σ := σ) (0 : ℤ))
    obtain ⟨k, Q, r, he, hr⟩ := exists_positive_pseudoDivision p q hq
    have hrem : FiniteSemialgebraicFunction (fun x : σ → ℝ =>
        rationalCauchyIndex (q.map (MvPolynomial.eval x)) (r.map (MvPolynomial.eval x))) := by
      rcases hr with hz | hlt
      · simpa [hz, rationalCauchyIndex_zero_denominator] using
          (FiniteSemialgebraicFunction.const (σ := σ) (0 : ℤ))
      · exact ih _ (hlt.trans_eq hd) _ rfl q
    have hnonzero := (finiteSemialgebraic_infinityVariation r q).map₂ hrem
      (fun a b : ℤ => a - b)
    have hb := herase.ite hnonzero (leadingCoeff_zero_semialgebraic q)
    convert hb using 1
    funext x
    by_cases hx : MvPolynomial.eval x q.leadingCoeff = 0
    · simp only [mem_setOf_eq, if_pos hx, eraseLead_map_of_leadingCoeff_zero q _ hx]
    · simp only [mem_setOf_eq, if_neg hx]
      have hp : 0 < (MvPolynomial.eval x q.leadingCoeff)^(2*k) := by
        rw [pow_mul]
        exact pow_pos (sq_pos_of_ne_zero hx) k
      have hqx : q.map (MvPolynomial.eval x) ≠ 0 := by
        apply Polynomial.leadingCoeff_ne_zero.mp
        rwa [leadingCoeff_map_of_leadingCoeff_ne_zero _ hx]
      have hex := congrArg (Polynomial.map (MvPolynomial.eval x)) he
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_add] at hex
      rw [← Polynomial.C_pow] at hex
      exact positive_pseudo_index_recurrence_total hp hex hqx

theorem tarskiQuery_eq_rationalCauchyIndex_total (p q : Polynomial ℝ) :
    tarskiQuery p q = rationalCauchyIndex (q * p.derivative) p := by
  by_cases hp : p = 0
  · simp [hp, tarskiQuery, rationalCauchyIndex_zero_denominator]
  · exact tarskiQuery_eq_rationalCauchyIndex hp q

theorem finiteSemialgebraic_tarskiQuery (p q : Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      tarskiQuery (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))) := by
  simpa only [Polynomial.map_mul, Polynomial.derivative_map,
    tarskiQuery_eq_rationalCauchyIndex_total] using
      (finiteSemialgebraic_rationalCauchyIndex (q*p.derivative) p)

theorem tarskiQuery_fiber_semialgebraic (p q : Polynomial (MvPolynomial σ ℝ)) (z : ℤ) :
    IsSemialgebraic {x : σ → ℝ |
      tarskiQuery (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x)) = z} :=
  (finiteSemialgebraic_tarskiQuery p q).fiber z

end RealAlgebraicGeometry
end BfgsVerification
