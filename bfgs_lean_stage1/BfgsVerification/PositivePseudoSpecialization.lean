import BfgsVerification.PositivePseudoDivision

/-! A single actual polynomial pseudo-division identity specializes uniformly
where the actual divisor leading coefficient is nonzero. Its even scaling
preserves all three sign tests at every actual specialized divisor root. -/
noncomputable section
open Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

theorem positive_pseudoDivision_specialize {p q Q r : Polynomial R} {k : ℕ}
    (he : (C q.leadingCoeff)^(2*k)*p=q*Q+r)
    (hr : r=0 ∨ r.natDegree<q.natDegree)
    (f : R →+* ℝ) (hf : f q.leadingCoeff≠0) :
    (r.map f=0 ∨ (r.map f).natDegree<(q.map f).natDegree) ∧
      ∀ t : ℝ, (q.map f).eval t=0 →
        ((p.map f).eval t=0 ↔ (r.map f).eval t=0) ∧
        (0<(p.map f).eval t ↔ 0<(r.map f).eval t) ∧
        (0≤(p.map f).eval t ↔ 0≤(r.map f).eval t) := by
  constructor
  · rcases hr with hz|hd
    · exact Or.inl (by rw [hz,Polynomial.map_zero])
    · right
      rw [natDegree_map_of_leadingCoeff_ne_zero f hf]
      exact natDegree_map_le.trans_lt hd
  · intro t ht
    have hev := congrArg (fun z : Polynomial R => (z.map f).eval t) he
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_add,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_add,ht,
      zero_mul,zero_add] at hev
    have hpos : 0<(f q.leadingCoeff)^(2*k) := by
      rw [pow_mul]
      exact pow_pos (sq_pos_of_ne_zero hf) k
    rw [← hev]
    exact ⟨(mul_eq_zero_iff_left hpos.ne').symm,
      (mul_pos_iff_of_pos_left hpos).symm,(mul_nonneg_iff_of_pos_left hpos).symm⟩

theorem exists_uniform_positive_pseudoDivision (p q : Polynomial R) (hq : q≠0) :
    ∃ (k : ℕ) (Q r : Polynomial R), (C q.leadingCoeff)^(2*k)*p=q*Q+r ∧
      (r=0 ∨ r.natDegree<q.natDegree) ∧
      ∀ f : R →+* ℝ, f q.leadingCoeff≠0 →
        (r.map f=0 ∨ (r.map f).natDegree<(q.map f).natDegree) ∧
        ∀ t : ℝ, (q.map f).eval t=0 →
          ((p.map f).eval t=0 ↔ (r.map f).eval t=0) ∧
          (0<(p.map f).eval t ↔ 0<(r.map f).eval t) ∧
          (0≤(p.map f).eval t ↔ 0≤(r.map f).eval t) := by
  obtain ⟨k,Q,r,he,hr⟩ := exists_positive_pseudoDivision p q hq
  exact ⟨k,Q,r,he,hr,fun f hf => positive_pseudoDivision_specialize he hr f hf⟩

end RealAlgebraicGeometry
end BfgsVerification
