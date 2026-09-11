import BfgsVerification.RealQuadraticElimination

/-! Global elimination of one scalar quadratic equality or sign condition,
with arbitrary polynomial coefficients in the retained parameters. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Finite σ]

def quadraticDiscriminant (a b c : MvPolynomial σ ℝ) : MvPolynomial σ ℝ := b^2-4*a*c

theorem quadraticDiscriminant_eval (a b c : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (quadraticDiscriminant a b c) =
      (MvPolynomial.eval x b)^2-4*MvPolynomial.eval x a*MvPolynomial.eval x c := by
  simp [quadraticDiscriminant]

theorem quadratic_zero_projection_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t=0} := by
  have h := ((isSemialgebraic_equal_zero a).inter
    ((isSemialgebraic_equal_zero b).compl.union (isSemialgebraic_equal_zero c))).union
      ((isSemialgebraic_equal_zero a).compl.inter (isSemialgebraic_nonnegative (quadraticDiscriminant a b c)))
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_union,mem_inter_iff,mem_compl_iff,quadraticDiscriminant_eval,
    exists_quadratic_zero_iff]

theorem quadratic_positive_projection_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      0<quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t} := by
  have h := (isSemialgebraic_positive a).union
    (((isSemialgebraic_equal_zero a).inter
      ((isSemialgebraic_equal_zero b).compl.union (isSemialgebraic_positive c))).union
      ((isSemialgebraic_positive (-a)).inter (isSemialgebraic_positive (quadraticDiscriminant a b c))))
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_union,mem_inter_iff,mem_compl_iff,quadraticDiscriminant_eval,
    MvPolynomial.eval_neg,neg_pos,exists_quadratic_positive_iff]

theorem quadratic_nonnegative_projection_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      0≤quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t} := by
  have h := (isSemialgebraic_positive a).union
    (((isSemialgebraic_equal_zero a).inter
      ((isSemialgebraic_equal_zero b).compl.union (isSemialgebraic_nonnegative c))).union
      ((isSemialgebraic_positive (-a)).inter (isSemialgebraic_nonnegative (quadraticDiscriminant a b c))))
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_union,mem_inter_iff,mem_compl_iff,quadraticDiscriminant_eval,
    MvPolynomial.eval_neg,neg_pos,exists_quadratic_nonnegative_iff]

theorem quadratic_forall_nonpositive_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t≤0} := by
  have h := (quadratic_positive_projection_semialgebraic a b c).compl
  simpa only [compl_setOf,not_exists,not_lt] using h

theorem quadratic_forall_negative_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t<0} := by
  have h := (quadratic_nonnegative_projection_semialgebraic a b c).compl
  simpa only [compl_setOf,not_exists,not_le] using h

theorem quadratic_forall_nonzero_semialgebraic (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t≠0} := by
  have h := (quadratic_zero_projection_semialgebraic a b c).compl
  simpa only [compl_setOf,not_exists] using h

end RealAlgebraicGeometry
end BfgsVerification
