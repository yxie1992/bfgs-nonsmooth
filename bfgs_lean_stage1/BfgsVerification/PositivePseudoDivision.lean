import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

/-! Leading-term cancellation over an integral domain. This is the first
algebraic step toward arbitrary-degree signed remainder elimination. -/
noncomputable section
open Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

def pseudoLeadingTerm (p q : Polynomial R) : Polynomial R :=
  C p.leadingCoeff * X^(p.natDegree-q.natDegree)

def pseudoStep (p q : Polynomial R) : Polynomial R :=
  C q.leadingCoeff*p-pseudoLeadingTerm p q*q

theorem pseudoStep_degree_lt {p q : Polynomial R} (hp : p≠0) (hq : q≠0)
    (hd : q.natDegree≤p.natDegree) : (pseudoStep p q).degree<p.degree := by
  have hlp : p.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr hp
  have hlq : q.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr hq
  have hp0 : C q.leadingCoeff*p≠0 := mul_ne_zero (C_ne_zero.mpr hlq) hp
  have hleft : (C q.leadingCoeff*p).degree=p.degree := degree_C_mul hlq
  have hright : (pseudoLeadingTerm p q*q).degree=p.degree := by
    rw [pseudoLeadingTerm,degree_mul,degree_C_mul_X_pow _ hlp,
      degree_eq_natDegree hq,degree_eq_natDegree hp,← Nat.cast_add,Nat.sub_add_cancel hd]
  have hlead : (C q.leadingCoeff*p).leadingCoeff=(pseudoLeadingTerm p q*q).leadingCoeff := by
    simp only [pseudoLeadingTerm,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_X_pow,mul_one]
    exact mul_comm _ _
  have h := degree_sub_lt (hleft.trans hright.symm) hp0 hlead
  rwa [hleft] at h

theorem exists_pseudoDivision (p q : Polynomial R) (hq : q≠0) :
    ∃ (k : ℕ) (Q r : Polynomial R), (C q.leadingCoeff)^k*p=q*Q+r ∧
      (r=0 ∨ r.natDegree<q.natDegree) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h N ih =>
    by_cases hp : p=0
    · subst p
      exact ⟨0,0,0,by simp,Or.inl rfl⟩
    by_cases hd : p.natDegree<q.natDegree
    · exact ⟨0,0,p,by simp,Or.inr hd⟩
    have hstep := pseudoStep_degree_lt hp hq (Nat.le_of_not_gt hd)
    by_cases hs : pseudoStep p q=0
    · refine ⟨1,pseudoLeadingTerm p q,0,?_,Or.inl rfl⟩
      simpa only [pow_one,add_zero,mul_comm] using sub_eq_zero.mp hs
    · have hsmall : (pseudoStep p q).natDegree<N :=
        (natDegree_lt_natDegree hs hstep).trans_eq hn
      obtain ⟨k,Q,r,he,hr⟩ := ih _ hsmall (pseudoStep p q) rfl
      refine ⟨k+1,Q+(C q.leadingCoeff)^k*pseudoLeadingTerm p q,r,?_,hr⟩
      dsimp only [pseudoStep] at he
      rw [pow_succ]
      linear_combination he

theorem exists_positive_pseudoDivision (p q : Polynomial R) (hq : q≠0) :
    ∃ (k : ℕ) (Q r : Polynomial R), (C q.leadingCoeff)^(2*k)*p=q*Q+r ∧
      (r=0 ∨ r.natDegree<q.natDegree) := by
  obtain ⟨k,Q,r,he,hr⟩ := exists_pseudoDivision p q hq
  refine ⟨k,(C q.leadingCoeff)^k*Q,(C q.leadingCoeff)^k*r,?_,?_⟩
  · rw [two_mul,pow_add]
    linear_combination (C q.leadingCoeff)^k*he
  · rcases hr with hr|hr
    · rw [hr,mul_zero]
      exact Or.inl rfl
    · right
      rw [← map_pow]
      exact (natDegree_C_mul_le _ r).trans_lt hr

end RealAlgebraicGeometry
end BfgsVerification
