import BfgsVerification.MixedLinearElimination
import BfgsVerification.SemialgebraicLinearProjection

/-! Constructive projection for mixed finite affine systems with arbitrary
polynomial coefficients in the retained variables. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem isSemialgebraic_marked {σ : Type*} [Finite σ]
    (s : Bool) (p q : MvPolynomial σ ℝ) :
    IsSemialgebraic {x | markedLE s (MvPolynomial.eval x p) (MvPolynomial.eval x q)} := by
  cases s
  · have h := isSemialgebraic_nonnegative (q-p)
    simpa only [markedLE, Bool.false_eq_true, if_false, MvPolynomial.eval_sub, sub_nonneg] using h
  · have h := isSemialgebraic_positive (q-p)
    simpa only [markedLE, if_true, MvPolynomial.eval_sub, sub_pos] using h

/-- Exact elimination of one coordinate from an arbitrary finite mixture of
strict and weak affine inequalities. All divisions disappear from the output. -/
theorem marked_linear_projection_semialgebraic {σ ι : Type*} [Finite σ] [Fintype ι]
    (s : ι → Bool) (a b : ι → MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, markedLE (s i) (MvPolynomial.eval x (a i)*t) (MvPolynomial.eval x (b i))} := by
  let Z : ι → Set (σ → ℝ) := fun i =>
    {x | MvPolynomial.eval x (a i) = 0 → markedLE (s i) 0 (MvPolynomial.eval x (b i))}
  let P : ι × ι → Set (σ → ℝ) := fun ij =>
    {x | MvPolynomial.eval x (a ij.1) < 0 → 0 < MvPolynomial.eval x (a ij.2) →
      markedLE (s ij.1 || s ij.2)
        (MvPolynomial.eval x (b ij.2)*MvPolynomial.eval x (a ij.1))
        (MvPolynomial.eval x (b ij.1)*MvPolynomial.eval x (a ij.2))}
  have hZ (i : ι) : IsSemialgebraic (Z i) := by
    have h := (isSemialgebraic_equal_zero (a i)).compl.union
      (isSemialgebraic_marked (s i) 0 (b i))
    convert h using 1
    ext x
    simp only [Z, mem_setOf_eq, mem_union, mem_compl_iff, MvPolynomial.eval_zero]
    tauto
  have hP (ij : ι × ι) : IsSemialgebraic (P ij) := by
    have h := ((isSemialgebraic_positive (-a ij.1)).inter
      (isSemialgebraic_positive (a ij.2))).compl.union
      (isSemialgebraic_marked (s ij.1 || s ij.2) (b ij.2*a ij.1) (b ij.1*a ij.2))
    convert h using 1
    ext x
    simp only [P, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff,
      MvPolynomial.eval_neg, neg_pos, MvPolynomial.eval_mul]
    tauto
  have h := (isSemialgebraic_forall_finite Z hZ).inter
    (isSemialgebraic_forall_finite P hP)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, Z, P, Prod.forall]
  exact exists_marked_affine_iff _ _ _

end RealAlgebraicGeometry
end BfgsVerification
