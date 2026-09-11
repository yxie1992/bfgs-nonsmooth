import BfgsVerification.FiniteRootRemainders

/-! Exact arbitrary-degree algebra contracts. These establish positive-scaled
remainder reduction and finite specialization coverage, not full projection. -/
noncomputable section
open Polynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def PositivePseudoDivisionTarget : Prop := ∀ {n : ℕ}
    (p q : Polynomial (MvPolynomial (Fin n) ℝ)), q≠0 →
    ∃ (k : ℕ) (Q r : Polynomial (MvPolynomial (Fin n) ℝ)),
      (C q.leadingCoeff)^(2*k)*p=q*Q+r ∧ (r=0 ∨ r.natDegree<q.natDegree)

theorem positivePseudoDivision : PositivePseudoDivisionTarget :=
  exists_positive_pseudoDivision

def PseudoDivisionSpecializationTarget : Prop := ∀ {n : ℕ}
    (p q : Polynomial (MvPolynomial (Fin n) ℝ)), q≠0 →
    ∃ (k : ℕ) (Q r : Polynomial (MvPolynomial (Fin n) ℝ)),
      (C q.leadingCoeff)^(2*k)*p=q*Q+r ∧ (r=0 ∨ r.natDegree<q.natDegree) ∧
      ∀ x : Vec n, MvPolynomial.eval x q.leadingCoeff≠0 →
        RootRemainderSigns (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))
          (r.map (MvPolynomial.eval x))

theorem pseudoDivisionSpecialization : PseudoDivisionSpecializationTarget := by
  intro n p q hq
  obtain ⟨k,Q,r,he,hr,hu⟩ := exists_uniform_positive_pseudoDivision p q hq
  exact ⟨k,Q,r,he,hr,fun x hx => hu (MvPolynomial.eval x) hx⟩

def FiniteRootRemaindersTarget : Prop := ∀ {n : ℕ}
    (p q : Polynomial (MvPolynomial (Fin n) ℝ)),
    ∃ r : Fin (q.natDegree+1) → Polynomial (MvPolynomial (Fin n) ℝ),
      ∀ x : Vec n, q.map (MvPolynomial.eval x)≠0 →
        ∃ i, RootRemainderSigns (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))
          ((r i).map (MvPolynomial.eval x))

theorem finiteRootRemainders : FiniteRootRemaindersTarget := by
  intro n p q
  obtain ⟨r,hr⟩ := exists_finite_root_remainders p q
  exact ⟨r,fun x hx => hr (MvPolynomial.eval x) hx⟩

end BfgsVerification
