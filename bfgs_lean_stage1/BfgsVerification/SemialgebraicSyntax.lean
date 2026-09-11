import BfgsVerification.ObjectiveDefinitions
import Mathlib.Algebra.MvPolynomial.Monad

/-! Genuine quantifier-free semialgebraic syntax: finite Boolean combinations
of polynomial equalities and strict polynomial inequalities over the reals.
No projection closure or path-decomposition property is built into the
definition. Those are separate mathematical obligations. -/
noncomputable section
open Set MvPolynomial

namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- A finite Boolean polynomial formula. In particular, quantifiers are absent. -/
inductive PolynomialFormula (σ : Type*) where
  | equalZero : MvPolynomial σ ℝ → PolynomialFormula σ
  | positive : MvPolynomial σ ℝ → PolynomialFormula σ
  | and : PolynomialFormula σ → PolynomialFormula σ → PolynomialFormula σ
  | not : PolynomialFormula σ → PolynomialFormula σ

def PolynomialFormula.Holds {σ : Type*} : PolynomialFormula σ → (σ → ℝ) → Prop
  | .equalZero p, x => MvPolynomial.eval x p = 0
  | .positive p, x => 0 < MvPolynomial.eval x p
  | .and p q, x => p.Holds x ∧ q.Holds x
  | .not p, x => ¬p.Holds x

/-- Standard finite-dimensional semialgebraicity, with an actual Boolean
polynomial witness. This predicate contains no desired geometric conclusions. -/
def IsSemialgebraic {σ : Type*} [Finite σ] (S : Set (σ → ℝ)) : Prop :=
  ∃ φ : PolynomialFormula σ, ∀ x, x ∈ S ↔ φ.Holds x

def PolynomialFormula.substitute {σ τ : Type*} (g : σ → MvPolynomial τ ℝ) :
    PolynomialFormula σ → PolynomialFormula τ
  | .equalZero p => .equalZero (MvPolynomial.bind₁ g p)
  | .positive p => .positive (MvPolynomial.bind₁ g p)
  | .and p q => .and (p.substitute g) (q.substitute g)
  | .not p => .not (p.substitute g)

theorem polynomial_substitution_eval {σ τ : Type*} (g : σ → MvPolynomial τ ℝ)
    (p : MvPolynomial σ ℝ) (x : τ → ℝ) :
    MvPolynomial.eval x (MvPolynomial.bind₁ g p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) p :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) x g p

theorem PolynomialFormula.holds_substitute {σ τ : Type*}
    (φ : PolynomialFormula σ) (g : σ → MvPolynomial τ ℝ) (x : τ → ℝ) :
    (φ.substitute g).Holds x ↔ φ.Holds (fun i => MvPolynomial.eval x (g i)) := by
  induction φ with
  | equalZero p => simp only [substitute,Holds,polynomial_substitution_eval]
  | positive p => simp only [substitute,Holds,polynomial_substitution_eval]
  | and p q hp hq => simp only [substitute,Holds,hp,hq]
  | not p hp => simp only [substitute,Holds,hp]

theorem IsSemialgebraic.polynomial_preimage {σ τ : Type*} [Finite σ] [Finite τ]
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) (g : σ → MvPolynomial τ ℝ) :
    IsSemialgebraic ((fun x : τ → ℝ => fun i => MvPolynomial.eval x (g i)) ⁻¹' S) := by
  obtain ⟨φ,hφ⟩ := hS
  exact ⟨φ.substitute g,fun x => (hφ _).trans (φ.holds_substitute g x).symm⟩

theorem isSemialgebraic_equal_zero {σ : Type*} [Finite σ] (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {x | MvPolynomial.eval x p = 0} := ⟨.equalZero p,fun _ => Iff.rfl⟩

theorem isSemialgebraic_positive {σ : Type*} [Finite σ] (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {x | 0 < MvPolynomial.eval x p} := ⟨.positive p,fun _ => Iff.rfl⟩

theorem IsSemialgebraic.compl {σ : Type*} [Finite σ] {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) : IsSemialgebraic Sᶜ := by
  obtain ⟨φ,hφ⟩ := hS
  exact ⟨.not φ,fun x => not_congr (hφ x)⟩

theorem IsSemialgebraic.inter {σ : Type*} [Finite σ] {S T : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  obtain ⟨φ,hφ⟩ := hS
  obtain ⟨ψ,hψ⟩ := hT
  exact ⟨.and φ ψ,fun x => and_congr (hφ x) (hψ x)⟩

theorem IsSemialgebraic.union {σ : Type*} [Finite σ] {S T : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∪ T) := by
  simpa only [compl_inter,compl_compl] using (hS.compl.inter hT.compl).compl

theorem isSemialgebraic_univ {σ : Type*} [Finite σ] :
    IsSemialgebraic (univ : Set (σ → ℝ)) := by
  refine ⟨.equalZero 0,?_⟩
  simp [PolynomialFormula.Holds]

theorem isSemialgebraic_empty {σ : Type*} [Finite σ] :
    IsSemialgebraic (∅ : Set (σ → ℝ)) := by
  simpa only [compl_univ] using (isSemialgebraic_univ (σ := σ)).compl

theorem isSemialgebraic_finset_union {σ ι : Type*} [Finite σ]
    (I : Finset ι) (S : ι → Set (σ → ℝ)) (hS : ∀ i ∈ I, IsSemialgebraic (S i)) :
    IsSemialgebraic (⋃ i ∈ I, S i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using isSemialgebraic_empty (σ := σ)
  | @insert i I hi ih =>
    have h := (hS i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.set_biUnion_insert] using h

end RealAlgebraicGeometry
end BfgsVerification
