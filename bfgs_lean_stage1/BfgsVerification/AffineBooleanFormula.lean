import BfgsVerification.SemialgebraicMixedProjection

/-! Finite Boolean formulas in affine inequalities and their exact disjunctive
normal form. This is a syntactic construction, with proved real semantics. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

structure AffineAtom (σ : Type*) where
  strict : Bool
  slope : MvPolynomial σ ℝ
  bound : MvPolynomial σ ℝ

def AffineAtom.Holds {σ : Type*} (a : AffineAtom σ) (x : σ → ℝ) (t : ℝ) : Prop :=
  markedLE a.strict (MvPolynomial.eval x a.slope*t) (MvPolynomial.eval x a.bound)

def AffineAtom.neg {σ : Type*} (a : AffineAtom σ) : AffineAtom σ :=
  ⟨!a.strict,-a.slope,-a.bound⟩

theorem AffineAtom.holds_neg {σ : Type*} (a : AffineAtom σ) (x : σ → ℝ) (t : ℝ) :
    a.neg.Holds x t ↔ ¬a.Holds x t := by
  cases a with
  | mk s a b => cases s <;> simp [neg,Holds,markedLE]

inductive AffineBooleanFormula (σ : Type*) where
  | atom : AffineAtom σ → AffineBooleanFormula σ
  | and : AffineBooleanFormula σ → AffineBooleanFormula σ → AffineBooleanFormula σ
  | not : AffineBooleanFormula σ → AffineBooleanFormula σ

def AffineBooleanFormula.Holds {σ : Type*} : AffineBooleanFormula σ → (σ → ℝ) → ℝ → Prop
  | .atom a,x,t => a.Holds x t
  | .and f g,x,t => f.Holds x t ∧ g.Holds x t
  | .not f,x,t => ¬f.Holds x t

abbrev AffineDNF (σ : Type*) := List (List (AffineAtom σ))

def AffineDNF.Holds {σ : Type*} (D : AffineDNF σ) (x : σ → ℝ) (t : ℝ) : Prop :=
  ∃ c ∈ D, ∀ a ∈ c, AffineAtom.Holds a x t

def AffineDNF.product {σ : Type*} (D E : AffineDNF σ) : AffineDNF σ :=
  D.flatMap (fun c => E.map (fun d => c++d))

theorem AffineDNF.holds_append {σ : Type*} (D E : AffineDNF σ) (x : σ → ℝ) (t : ℝ) :
    AffineDNF.Holds (D++E) x t ↔ D.Holds x t ∨ E.Holds x t := by
  simp only [Holds,List.mem_append]
  aesop

theorem AffineDNF.holds_product {σ : Type*} (D E : AffineDNF σ) (x : σ → ℝ) (t : ℝ) :
    (D.product E).Holds x t ↔ D.Holds x t ∧ E.Holds x t := by
  simp only [Holds,product,List.mem_flatMap,List.mem_map,List.mem_append]
  aesop

/-- Negations are pushed to atoms and conjunctions distributed explicitly. -/
def AffineBooleanFormula.toDNF {σ : Type*} : Bool → AffineBooleanFormula σ → AffineDNF σ
  | b,.atom a => [[if b then a.neg else a]]
  | false,.and f g => (f.toDNF false).product (g.toDNF false)
  | true,.and f g => f.toDNF true ++ g.toDNF true
  | b,.not f => f.toDNF (!b)

theorem AffineBooleanFormula.holds_toDNF {σ : Type*} (f : AffineBooleanFormula σ)
    (b : Bool) (x : σ → ℝ) (t : ℝ) :
    (f.toDNF b).Holds x t ↔ if b then ¬f.Holds x t else f.Holds x t := by
  induction f generalizing b with
  | atom a =>
    cases b <;> simp [toDNF,AffineDNF.Holds,Holds,AffineAtom.holds_neg]
  | and f g hf hg =>
    cases b <;> simp only [toDNF,AffineDNF.holds_product,AffineDNF.holds_append,
      hf,hg,Holds,Bool.false_eq_true,if_false,if_true] <;> tauto
  | not f hf =>
    cases b <;> simp [toDNF,hf,Holds]

end RealAlgebraicGeometry
end BfgsVerification
