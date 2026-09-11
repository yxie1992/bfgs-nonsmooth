import BfgsVerification.SemialgebraicCurveGraphs

noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

/-- Concatenation preserves the genuine graph on the closed unit interval.
The two affine preimages are intersected with their actual half intervals. -/
theorem IsSemialgebraicCurveOn.joinedCurve {p q : ℝ → σ → ℝ}
    (hp : IsSemialgebraicCurveOn p (Icc 0 1))
    (hq : IsSemialgebraicCurveOn q (Icc 0 1)) :
    IsSemialgebraicCurveOn (joinedCurve p q) (Icc 0 1) := by
  let PL : Option σ → MvPolynomial (Option σ) ℝ :=
    fun i => Option.elim i (C 2 * X none) (fun j => X (some j))
  let PR : Option σ → MvPolynomial (Option σ) ℝ :=
    fun i => Option.elim i (C 2 * X none - C 1) (fun j => X (some j))
  have hL := ((semialgebraic_curve_interval (σ := σ) 0 1).inter
    (isSemialgebraic_nonnegative (C (1/2 : ℝ) - X none : MvPolynomial (Option σ) ℝ))).inter
    (hp.polynomial_preimage PL)
  have hR := ((semialgebraic_curve_interval (σ := σ) 0 1).inter
    (isSemialgebraic_positive (X none - C (1/2 : ℝ) : MvPolynomial (Option σ) ℝ))).inter
    (hq.polynomial_preimage PR)
  unfold IsSemialgebraicCurveOn
  convert hL.union hR using 1
  ext v
  simp only [mem_union,mem_inter_iff,mem_setOf_eq,mem_preimage,PL,PR,
    Option.elim_none,Option.elim_some,MvPolynomial.eval_sub,MvPolynomial.eval_mul,
    MvPolynomial.eval_C,MvPolynomial.eval_X,sub_nonneg,sub_pos]
  constructor
  · rintro ⟨ht,he⟩
    by_cases hl : v none ≤ 1/2
    · left
      have ht' : 2*v none ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1],by linarith⟩
      exact ⟨⟨ht,hl⟩,ht',by simpa only [BfgsVerification.RealAlgebraicGeometry.joinedCurve,if_pos hl] using he⟩
    · right
      have ht' : 2*v none-1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith,by linarith [ht.2]⟩
      exact ⟨⟨ht,lt_of_not_ge hl⟩,ht',by simpa only [BfgsVerification.RealAlgebraicGeometry.joinedCurve,if_neg hl] using he⟩
  · rintro (⟨⟨ht,hl⟩,_,he⟩ | ⟨⟨ht,hr⟩,_,he⟩)
    · exact ⟨ht,by simpa only [BfgsVerification.RealAlgebraicGeometry.joinedCurve,if_pos hl] using he⟩
    · exact ⟨ht,by simpa only [BfgsVerification.RealAlgebraicGeometry.joinedCurve,if_neg (not_le.mpr hr)] using he⟩

end RealAlgebraicGeometry
end BfgsVerification
