import BfgsVerification.SemialgebraicSyntax
import BfgsVerification.SemialgebraicLinearProjection
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Sign

/-! Finite-valued functions with genuine quantifier-free polynomial fibers.
This contains no projection or query oracle. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ α β γ : Type*} [Finite σ]

structure FiniteSemialgebraicFunction (f : (σ → ℝ) → α) : Prop where
  finite_range : (Set.range f).Finite
  fiber : ∀ a, IsSemialgebraic {x | f x = a}

theorem FiniteSemialgebraicFunction.const (a : α) :
    FiniteSemialgebraicFunction (fun _ : σ → ℝ => a) := by
  refine ⟨Set.finite_range_const, fun b => ?_⟩
  by_cases h : a = b
  · simpa [h] using (isSemialgebraic_univ (σ := σ))
  · simpa [h] using (isSemialgebraic_empty (σ := σ))

theorem FiniteSemialgebraicFunction.predicate {f : (σ → ℝ) → α}
    (hf : FiniteSemialgebraicFunction f) (P : α → Prop) :
    IsSemialgebraic {x | P (f x)} := by
  classical
  have h := isSemialgebraic_finset_union (hf.finite_range.toFinset.filter P)
    (fun a => {x | f x = a}) (fun a _ => hf.fiber a)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · intro hx
    exact ⟨f x, ⟨Set.mem_range_self x, hx⟩, rfl⟩
  · rintro ⟨a, ⟨_, ha⟩, hx⟩
    simpa only [hx] using ha

theorem FiniteSemialgebraicFunction.map {f : (σ → ℝ) → α}
    (hf : FiniteSemialgebraicFunction f) (g : α → β) :
    FiniteSemialgebraicFunction (fun x => g (f x)) := by
  refine ⟨?_, fun b => hf.predicate (fun a => g a = b)⟩
  simpa only [← Set.range_comp, Function.comp_def] using hf.finite_range.image g

theorem FiniteSemialgebraicFunction.pair {f : (σ → ℝ) → α} {g : (σ → ℝ) → β}
    (hf : FiniteSemialgebraicFunction f) (hg : FiniteSemialgebraicFunction g) :
    FiniteSemialgebraicFunction (fun x => (f x, g x)) := by
  refine ⟨(hf.finite_range.prod hg.finite_range).subset ?_, fun ab => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨Set.mem_range_self x, Set.mem_range_self x⟩
  · rcases ab with ⟨a, b⟩
    simpa only [Prod.mk.injEq, setOf_and] using (hf.fiber a).inter (hg.fiber b)

theorem FiniteSemialgebraicFunction.map₂ {f : (σ → ℝ) → α} {g : (σ → ℝ) → β}
    (hf : FiniteSemialgebraicFunction f) (hg : FiniteSemialgebraicFunction g)
    (h : α → β → γ) : FiniteSemialgebraicFunction (fun x => h (f x) (g x)) :=
  (hf.pair hg).map (fun ab => h ab.1 ab.2)

theorem FiniteSemialgebraicFunction.ite {f g : (σ → ℝ) → α}
    (hf : FiniteSemialgebraicFunction f) (hg : FiniteSemialgebraicFunction g)
    {S : Set (σ → ℝ)} [DecidablePred (· ∈ S)] (hS : IsSemialgebraic S) :
    FiniteSemialgebraicFunction (fun x => if x ∈ S then f x else g x) := by
  classical
  refine ⟨Set.finite_range_ite hf.finite_range hg.finite_range, fun a => ?_⟩
  have h := (hS.inter (hf.fiber a)).union (hS.compl.inter (hg.fiber a))
  convert h using 1
  ext x
  by_cases hx : x ∈ S <;> simp [hx]

theorem finiteSemialgebraic_polynomial_sign (p : MvPolynomial σ ℝ) :
    FiniteSemialgebraicFunction (fun x => SignType.sign (MvPolynomial.eval x p)) := by
  refine ⟨(Set.toFinite _), ?_⟩
  intro s
  cases s with
  | zero => simpa using (isSemialgebraic_equal_zero p)
  | pos =>
    change IsSemialgebraic {x | SignType.sign (MvPolynomial.eval x p) = 1}
    simpa only [sign_eq_one_iff] using (isSemialgebraic_positive p)
  | neg =>
    change IsSemialgebraic {x | SignType.sign (MvPolynomial.eval x p) = -1}
    simpa only [sign_eq_neg_one_iff, map_neg, neg_pos] using
      (isSemialgebraic_positive (-p))

theorem FiniteSemialgebraicFunction.sum {ι A : Type*} [AddCommMonoid A]
    (I : Finset ι) (f : ι → (σ → ℝ) → A)
    (hf : ∀ i ∈ I, FiniteSemialgebraicFunction (f i)) :
    FiniteSemialgebraicFunction (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (FiniteSemialgebraicFunction.const (σ := σ) (0 : A))
  | @insert i I hi ih =>
    have h := (hf i (Finset.mem_insert_self i I)).map₂
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (fun a b : A => a+b)
    simpa only [Finset.sum_insert hi] using h

theorem FiniteSemialgebraicFunction.select {f : (σ → ℝ) → α}
    (hf : FiniteSemialgebraicFunction f) (g : α → (σ → ℝ) → β)
    (hg : ∀ a, FiniteSemialgebraicFunction (g a)) :
    FiniteSemialgebraicFunction (fun x => g (f x) x) := by
  classical
  refine ⟨?_, fun b => ?_⟩
  · apply (hf.finite_range.biUnion (fun a _ => (hg a).finite_range)).subset
    rintro _ ⟨x, rfl⟩
    exact Set.mem_iUnion.mpr ⟨f x, Set.mem_iUnion.mpr
      ⟨Set.mem_range_self x, Set.mem_range_self x⟩⟩
  · have h := isSemialgebraic_finset_union hf.finite_range.toFinset
      (fun a => {x | f x = a} ∩ {x | g a x = b})
      (fun a _ => (hf.fiber a).inter ((hg a).fiber b))
    convert h using 1
    ext x
    simp only [mem_setOf_eq, mem_iUnion, Set.Finite.mem_toFinset, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨f x, Set.mem_range_self x, rfl, hx⟩
    · rintro ⟨a, _, ha, hx⟩
      simpa only [ha] using hx

end RealAlgebraicGeometry
end BfgsVerification
