import BfgsVerification.RationalGlobalReciprocity

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem rationalCauchyIndex_zero_numerator (q : Polynomial ℝ) : rationalCauchyIndex 0 q = 0 := by
  classical
  unfold rationalCauchyIndex
  apply Finset.sum_eq_zero
  intro a _
  apply localCauchyIndex_of_finite_left_limit (b := 0)
  simp only [eval_zero, zero_div]
  exact tendsto_const_nhds

theorem rationalCauchyIndex_zero_denominator (p : Polynomial ℝ) : rationalCauchyIndex p 0 = 0 := by
  classical
  simp [rationalCauchyIndex]

theorem rationalCauchyIndex_euclidean_recurrence (p : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) (hr : p % q ≠ 0) :
    rationalCauchyIndex p q = infinityVariation (p%q) q-rationalCauchyIndex q (p%q) := by
  have hm := rationalCauchyIndex_mod p hq
  have he := rationalCauchyIndex_reciprocity hr hq
  omega

/-- A finite Euclidean index calculation. Correctness derives a sufficient degree bound. -/
def euclideanIndexAux : ℕ → Polynomial ℝ → Polynomial ℝ → ℤ
  | 0, _, _ => 0
  | k+1, p, q => by
    classical
    exact if q=0 ∨ p%q=0 then 0
      else infinityVariation (p%q) q-euclideanIndexAux k q (p%q)

theorem euclideanIndexAux_correct (k : ℕ) (p q : Polynomial ℝ)
    (hk : q.natDegree < k) : euclideanIndexAux k p q = rationalCauchyIndex p q := by
  classical
  induction k generalizing p q with
  | zero => omega
  | succ k ih =>
    by_cases hq : q=0
    · simp [euclideanIndexAux, hq, rationalCauchyIndex_zero_denominator]
    by_cases hr : p%q=0
    · have he := rationalCauchyIndex_mod p hq
      rw [hr, rationalCauchyIndex_zero_numerator] at he
      simp [euclideanIndexAux, hr, he]
    have hd : (p%q).natDegree < q.natDegree :=
      Polynomial.natDegree_lt_natDegree hr (EuclideanDomain.mod_lt p hq)
    have hbound : (p%q).natDegree < k := by omega
    rw [euclideanIndexAux, if_neg (not_or_intro hq hr), ih q (p%q) hbound]
    exact (rationalCauchyIndex_euclidean_recurrence p hq hr).symm

/-- The degree-bounded exact integer index obtained from actual polynomial division. -/
def euclideanIndex (p q : Polynomial ℝ) : ℤ := euclideanIndexAux (q.natDegree+1) p q

theorem euclideanIndex_correct (p q : Polynomial ℝ) :
    euclideanIndex p q = rationalCauchyIndex p q :=
  euclideanIndexAux_correct _ _ _ (Nat.lt_succ_self _)

theorem tarskiQuery_eq_euclideanIndex {p : Polynomial ℝ} (hp : p ≠ 0) (q : Polynomial ℝ) :
    tarskiQuery p q = euclideanIndex (q*p.derivative) p := by
  rw [euclideanIndex_correct]
  exact tarskiQuery_eq_rationalCauchyIndex hp q

end RealAlgebraicGeometry
end BfgsVerification
