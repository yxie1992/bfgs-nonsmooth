import BfgsVerification.PolynomialSignJumps

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem polynomialRightSign_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (a : ℝ) :
    polynomialRightSign (p*q) a = polynomialRightSign p a * polynomialRightSign q a := by
  have h := (polynomial_sign_right_of_rootMultiplicity (mul_ne_zero hp hq) a).and
    ((polynomial_sign_right_of_rootMultiplicity hp a).and
      (polynomial_sign_right_of_rootMultiplicity hq a))
  obtain ⟨x,hpq,hpx,hqx⟩ := h.exists
  have he := congrArg (fun s : SignType => (s : ℤ)) hpq
  rw [eval_mul, sign_mul, hpx, hqx] at he
  simpa only [SignType.coe_mul, polynomialRightSign] using he.symm

theorem localCauchyIndex_reciprocity_twice {p q : Polynomial ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (a : ℝ) :
    2 * (localCauchyIndex (fun x => p.eval x/q.eval x) a +
      localCauchyIndex (fun x => q.eval x/p.eval x) a) =
        polynomialRightSign (p*q) a-polynomialLeftSign (p*q) a := by
  rw [localCauchyIndex_rational_reciprocity hp hq a, polynomialLeftSign,
    Polynomial.rootMultiplicity_mul (mul_ne_zero hp hq), polynomialRightSign_mul hp hq]
  by_cases ho : Odd (p.rootMultiplicity a+q.rootMultiplicity a)
  · rw [if_pos ho, ho.neg_one_pow, sign_mul, SignType.coe_mul]
    change 2*(polynomialRightSign p a*polynomialRightSign q a) = _
    ring
  · have he := Nat.not_odd_iff_even.mp ho
    rw [if_neg ho, he.neg_one_pow]
    ring

theorem rationalCauchyIndex_extend_roots {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    rationalCauchyIndex p q =
      ∑ a ∈ (p*q).roots.toFinset, localCauchyIndex (fun x => p.eval x/q.eval x) a := by
  classical
  unfold rationalCauchyIndex
  apply Finset.sum_subset
  · rw [Polynomial.roots_mul (mul_ne_zero hp hq), Multiset.toFinset_add]
    exact Finset.subset_union_right
  · intro a _ ha
    have hn : q.eval a ≠ 0 := fun hr =>
      ha (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hr))
    apply localCauchyIndex_zero_of_order_le p hq a
    rw [Polynomial.rootMultiplicity_eq_zero hn]
    exact Nat.zero_le _

theorem rationalCauchyIndex_reciprocity_twice {p q : Polynomial ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    2*(rationalCauchyIndex p q+rationalCauchyIndex q p) =
      (SignType.sign (p*q).leadingCoeff : ℤ) -
        (-1 : ℤ)^(p*q).natDegree * (SignType.sign (p*q).leadingCoeff : ℤ) := by
  classical
  rw [rationalCauchyIndex_extend_roots hp hq, rationalCauchyIndex_extend_roots hq hp]
  rw [show q*p = p*q from mul_comm _ _]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [localCauchyIndex_reciprocity_twice hp hq]
  exact polynomial_sign_jump_sum (mul_ne_zero hp hq)

/-- Endpoint sign contribution in full-line rational-index reciprocity. -/
def infinityVariation (p q : Polynomial ℝ) : ℤ :=
  ((SignType.sign (p*q).leadingCoeff : ℤ) -
    (-1 : ℤ)^(p*q).natDegree * (SignType.sign (p*q).leadingCoeff : ℤ))/2

theorem rationalCauchyIndex_reciprocity {p q : Polynomial ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    rationalCauchyIndex p q+rationalCauchyIndex q p = infinityVariation p q := by
  have he := rationalCauchyIndex_reciprocity_twice hp hq
  unfold infinityVariation
  omega

end RealAlgebraicGeometry
end BfgsVerification
