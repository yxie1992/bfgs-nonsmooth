import BfgsVerification.LinearElimination
import BfgsVerification.SemialgebraicGraphs

/-! Genuine one-coordinate projection for finite strict or weak systems affine
in the eliminated variable, with arbitrary polynomial parameter coefficients.
This is a proved special case, not general polynomial quantifier elimination. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem isSemialgebraic_forall_finite {σ ι : Type*} [Finite σ] [Fintype ι]
    (S : ι → Set (σ → ℝ)) (hS : ∀ i, IsSemialgebraic (S i)) :
    IsSemialgebraic {x | ∀ i, x ∈ S i} := by
  have h := isSemialgebraic_finset_inter Finset.univ S (fun i _ => hS i)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, Finset.mem_univ, mem_iInter, forall_const]

/-- Strict affine inequalities, including identically zero coefficients and
unbounded or empty fibers, have an explicit polynomial sign criterion. -/
theorem strict_linear_projection_semialgebraic {σ ι : Type*} [Finite σ] [Fintype ι]
    (a b : ι → MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, MvPolynomial.eval x (a i) * t < MvPolynomial.eval x (b i)} := by
  let Z : ι → Set (σ → ℝ) := fun i =>
    {x | MvPolynomial.eval x (a i) = 0 → 0 < MvPolynomial.eval x (b i)}
  let P : ι × ι → Set (σ → ℝ) := fun ij =>
    {x | MvPolynomial.eval x (a ij.1) < 0 → 0 < MvPolynomial.eval x (a ij.2) →
      MvPolynomial.eval x (b ij.2) * MvPolynomial.eval x (a ij.1) <
        MvPolynomial.eval x (b ij.1) * MvPolynomial.eval x (a ij.2)}
  have hZ (i : ι) : IsSemialgebraic (Z i) := by
    have h := (isSemialgebraic_equal_zero (a i)).compl.union
      (isSemialgebraic_positive (b i))
    convert h using 1
    ext x
    simp only [Z, mem_setOf_eq, mem_union, mem_compl_iff]
    tauto
  have hP (ij : ι × ι) : IsSemialgebraic (P ij) := by
    have h := ((isSemialgebraic_positive (-a ij.1)).inter
      (isSemialgebraic_positive (a ij.2))).compl.union
      (isSemialgebraic_positive (b ij.1 * a ij.2 - b ij.2 * a ij.1))
    convert h using 1
    ext x
    simp only [P, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff,
      MvPolynomial.eval_neg, neg_pos, MvPolynomial.eval_sub, MvPolynomial.eval_mul, sub_pos]
    tauto
  have h := (isSemialgebraic_forall_finite Z hZ).inter
    (isSemialgebraic_forall_finite P hP)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, Z, P, Prod.forall]
  exact exists_strict_affine_iff _ _

/-- The weak version retains feasible touching bounds, with non-strict
cross-products. No generic projection-closure theorem is assumed. -/
theorem weak_linear_projection_semialgebraic {σ ι : Type*} [Finite σ] [Fintype ι]
    (a b : ι → MvPolynomial σ ℝ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, MvPolynomial.eval x (a i) * t ≤ MvPolynomial.eval x (b i)} := by
  let Z : ι → Set (σ → ℝ) := fun i =>
    {x | MvPolynomial.eval x (a i) = 0 → 0 ≤ MvPolynomial.eval x (b i)}
  let P : ι × ι → Set (σ → ℝ) := fun ij =>
    {x | MvPolynomial.eval x (a ij.1) < 0 → 0 < MvPolynomial.eval x (a ij.2) →
      MvPolynomial.eval x (b ij.2) * MvPolynomial.eval x (a ij.1) ≤
        MvPolynomial.eval x (b ij.1) * MvPolynomial.eval x (a ij.2)}
  have hZ (i : ι) : IsSemialgebraic (Z i) := by
    have h := (isSemialgebraic_equal_zero (a i)).compl.union
      (isSemialgebraic_nonnegative (b i))
    convert h using 1
    ext x
    simp only [Z, mem_setOf_eq, mem_union, mem_compl_iff]
    tauto
  have hP (ij : ι × ι) : IsSemialgebraic (P ij) := by
    have h := ((isSemialgebraic_positive (-a ij.1)).inter
      (isSemialgebraic_positive (a ij.2))).compl.union
      (isSemialgebraic_nonnegative (b ij.1 * a ij.2 - b ij.2 * a ij.1))
    convert h using 1
    ext x
    simp only [P, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff,
      MvPolynomial.eval_neg, neg_pos, MvPolynomial.eval_sub, MvPolynomial.eval_mul, sub_nonneg]
    tauto
  have h := (isSemialgebraic_forall_finite Z hZ).inter
    (isSemialgebraic_forall_finite P hP)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, Z, P, Prod.forall]
  exact exists_weak_affine_iff _ _

end RealAlgebraicGeometry
end BfgsVerification
