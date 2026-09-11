import BfgsVerification.SemialgebraicSyntax

/-! Actual objective graphs and elementary polynomial examples for the genuine
semialgebraic predicate. No quantified projection result is used here. -/
noncomputable section
open scoped BigOperators
open Set MvPolynomial

namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem isSemialgebraic_finset_inter {σ ι : Type*} [Finite σ]
    (I : Finset ι) (S : ι → Set (σ → ℝ)) (hS : ∀ i ∈ I, IsSemialgebraic (S i)) :
    IsSemialgebraic (⋂ i ∈ I, S i) := by
  have h := (isSemialgebraic_finset_union I (fun i => (S i)ᶜ)
    (fun i hi => (hS i hi).compl)).compl
  simpa only [compl_iUnion,compl_compl] using h

theorem isSemialgebraic_nonnegative {σ : Type*} [Finite σ] (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {x | 0 ≤ MvPolynomial.eval x p} := by
  have h := (isSemialgebraic_positive (-p)).compl
  simpa only [MvPolynomial.eval_neg,neg_pos,compl_setOf,not_lt] using h

/-- The additional `none` coordinate is the actual output value. -/
def objectiveGraph {n : ℕ} (F : Vec n → ℝ) : Set (Option (Fin n) → ℝ) :=
  {v | v none = F (fun i => v (some i))}

def IsSemialgebraicObjective {n : ℕ} (F : Vec n → ℝ) : Prop :=
  IsSemialgebraic (objectiveGraph F)

theorem polynomial_objective_semialgebraic {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraicObjective (fun x => MvPolynomial.eval x p) := by
  change IsSemialgebraic (objectiveGraph (fun x => MvPolynomial.eval x p))
  have h := isSemialgebraic_equal_zero
    (MvPolynomial.X none - MvPolynomial.rename some p)
  convert h using 1
  ext v
  simp only [objectiveGraph,mem_setOf_eq,MvPolynomial.eval_sub,MvPolynomial.eval_X,
    MvPolynomial.eval_rename,Function.comp_def,sub_eq_zero]

theorem finite_polynomial_max_semialgebraic {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℝ) (F : Vec n → ℝ)
    (hF : ∀ x, IsGreatest (range (fun i => MvPolynomial.eval x (p i))) (F x)) :
    IsSemialgebraicObjective F := by
  change IsSemialgebraic (objectiveGraph F)
  let E : Fin m → Set (Option (Fin n) → ℝ) := fun i =>
    {v | v none = MvPolynomial.eval (fun j => v (some j)) (p i)}
  let L : Fin m → Set (Option (Fin n) → ℝ) := fun i =>
    {v | MvPolynomial.eval (fun j => v (some j)) (p i) ≤ v none}
  have hE : ∀ i, IsSemialgebraic (E i) := fun i => polynomial_objective_semialgebraic (p i)
  have hL : ∀ i, IsSemialgebraic (L i) := by
    intro i
    have h := isSemialgebraic_nonnegative
      (MvPolynomial.X none - MvPolynomial.rename some (p i))
    convert h using 1
    ext v
    simp only [L,mem_setOf_eq,MvPolynomial.eval_sub,MvPolynomial.eval_X,
      MvPolynomial.eval_rename,Function.comp_def,sub_nonneg]
  have h := (isSemialgebraic_finset_union Finset.univ E (fun i _ => hE i)).inter
    (isSemialgebraic_finset_inter Finset.univ L (fun i _ => hL i))
  convert h using 1
  ext v
  simp only [objectiveGraph,mem_setOf_eq,mem_inter_iff,mem_iUnion,mem_iInter,
    Finset.mem_univ,true_and,forall_const,exists_prop,E,L]
  constructor
  · intro hv
    obtain ⟨i,hi⟩ := (hF (fun j => v (some j))).1
    refine ⟨⟨i,?_⟩,?_⟩
    · exact hv.trans hi.symm
    · intro j
      rw [hv]
      exact (hF _).2 (mem_range_self j)
  · rintro ⟨⟨i,hi⟩,hupper⟩
    apply le_antisymm
    · rw [hi]
      exact (hF _).2 (mem_range_self i)
    · obtain ⟨j,hj⟩ := (hF (fun k => v (some k))).1
      rw [← hj]
      exact hupper j

end RealAlgebraicGeometry
end BfgsVerification
