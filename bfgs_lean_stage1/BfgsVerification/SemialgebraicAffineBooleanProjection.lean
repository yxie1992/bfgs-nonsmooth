import BfgsVerification.AffineBooleanFormula
import BfgsVerification.SemialgebraicSupportProjection

/-! Proved coordinate projection for arbitrary finite Boolean combinations of
inequalities affine in one eliminated coordinate. Retained-coordinate
coefficients may be arbitrary polynomials; general polynomial projection is
not assumed or claimed. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem affine_clause_projection_semialgebraic {σ : Type*} [Finite σ]
    (c : List (AffineAtom σ)) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ, ∀ a ∈ c, AffineAtom.Holds a x t} := by
  classical
  let I := c.toFinset
  have h := marked_linear_projection_semialgebraic
    (fun a : I => a.val.strict) (fun a : I => a.val.slope) (fun a : I => a.val.bound)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, Subtype.forall, I, List.mem_toFinset, AffineAtom.Holds]

theorem affine_dnf_projection_semialgebraic {σ : Type*} [Finite σ]
    (D : AffineDNF σ) : IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ, D.Holds x t} := by
  classical
  have h := isSemialgebraic_finset_union D.toFinset
    (fun c => {x : σ → ℝ | ∃ t : ℝ, ∀ a ∈ c, AffineAtom.Holds a x t})
    (fun c _ => affine_clause_projection_semialgebraic c)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_iUnion, List.mem_toFinset, AffineDNF.Holds]
  aesop

/-- One existential quantifier is actually eliminated for every finite Boolean
formula of affine inequalities, including all negations and weak boundaries. -/
theorem affine_boolean_projection_semialgebraic {σ : Type*} [Finite σ]
    (f : AffineBooleanFormula σ) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ, f.Holds x t} := by
  have h := affine_dnf_projection_semialgebraic (f.toDNF false)
  simpa only [f.holds_toDNF, Bool.false_eq_true, if_false] using h

/-- The actual polynomial whose positive sign expresses an affine atom. -/
def AffineAtom.polynomial {σ : Type*} (a : AffineAtom σ) :
    MvPolynomial (σ ⊕ Unit) ℝ :=
  MvPolynomial.rename Sum.inl a.bound - MvPolynomial.rename Sum.inl a.slope * X (.inr ())

def AffineAtom.toPolynomialFormula {σ : Type*} (a : AffineAtom σ) :
    PolynomialFormula (σ ⊕ Unit) :=
  if a.strict then .positive a.polynomial else .not (.positive (-a.polynomial))

theorem AffineAtom.polynomial_eval {σ : Type*} (a : AffineAtom σ) (x : σ → ℝ) (t : ℝ) :
    MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) a.polynomial =
      MvPolynomial.eval x a.bound - MvPolynomial.eval x a.slope * t := by
  simp [polynomial,MvPolynomial.eval_rename,Function.comp_def]

theorem AffineAtom.holds_polynomialFormula {σ : Type*}
    (a : AffineAtom σ) (x : σ → ℝ) (t : ℝ) :
    a.toPolynomialFormula.Holds (Sum.elim x (fun _ : Unit => t)) ↔ a.Holds x t := by
  cases hs : a.strict <;> simp [toPolynomialFormula,hs,PolynomialFormula.Holds,
    polynomial_eval,AffineAtom.Holds,markedLE]

def AffineBooleanFormula.toPolynomialFormula {σ : Type*} :
    AffineBooleanFormula σ → PolynomialFormula (σ ⊕ Unit)
  | .atom a => a.toPolynomialFormula
  | .and f g => .and f.toPolynomialFormula g.toPolynomialFormula
  | .not f => .not f.toPolynomialFormula

theorem AffineBooleanFormula.holds_polynomialFormula {σ : Type*}
    (f : AffineBooleanFormula σ) (x : σ → ℝ) (t : ℝ) :
    f.toPolynomialFormula.Holds (Sum.elim x (fun _ : Unit => t)) ↔ f.Holds x t := by
  induction f with
  | atom a => exact a.holds_polynomialFormula x t
  | and f g hf hg => exact and_congr hf hg
  | not f hf => exact not_congr hf

/-- Literal coordinate-projection form: the input is a genuine Boolean
polynomial set and the output has a proved quantifier-free polynomial witness. -/
theorem affine_boolean_coordinate_projection {σ : Type*} [Finite σ]
    (f : AffineBooleanFormula σ) :
    IsSemialgebraic (coordinateProjection {v : (σ ⊕ Unit) → ℝ | f.toPolynomialFormula.Holds v}) := by
  have h := affine_boolean_projection_semialgebraic f
  convert h using 1
  ext x
  change (∃ y : Unit → ℝ, f.toPolynomialFormula.Holds (Sum.elim x y)) ↔ ∃ t, f.Holds x t
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨y (), ?_⟩
    have he : y = fun _ : Unit => y () := by funext u; cases u; rfl
    rw [he] at hy
    exact (f.holds_polynomialFormula x (y ())).mp hy
  · rintro ⟨t,ht⟩
    exact ⟨fun _ => t,(f.holds_polynomialFormula x t).mpr ht⟩

end RealAlgebraicGeometry
end BfgsVerification
