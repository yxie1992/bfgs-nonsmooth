import BfgsVerification.BooleanPolynomialProjection
import BfgsVerification.SemialgebraicSupportProjection
import Mathlib.Data.Finite.Sum

/-! Global finite-coordinate projection closure of genuine quantifier-free
semialgebraic sets. Every scalar elimination is the actual polynomial
sign-query construction proved in this import chain. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry
universe u v

theorem IsSemialgebraic.reindex {σ τ : Type*} [Finite σ] [Finite τ]
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) (r : σ → τ) :
    IsSemialgebraic {x : τ → ℝ | (fun i => x (r i)) ∈ S} := by
  simpa only [MvPolynomial.eval_X] using hS.polynomial_preimage (fun i => X (r i))

def optionProjectionReindex {σ τ : Type*} : σ ⊕ Option τ → Option (σ ⊕ τ)
  | .inl i => some (.inl i)
  | .inr none => none
  | .inr (some j) => some (.inr j)

theorem optionProjectionReindex_eval {σ τ : Type*}
    (x : σ → ℝ) (y : τ → ℝ) (t : ℝ) :
    (fun j => Option.elim (optionProjectionReindex j) t (Sum.elim x y)) =
      Sum.elim x (fun j => Option.elim j t y) := by
  funext j
  rcases j with i | (_ | j) <;> rfl

theorem coordinate_projection_semialgebraic {σ : Type u} {τ : Type v} [Finite σ] [Finite τ]
    {S : Set ((σ ⊕ τ) → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (coordinateProjection S) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  suffices H : ∀ (τ : Type v) [Finite τ], ∀ (S : Set ((σ ⊕ τ) → ℝ)),
      IsSemialgebraic S → IsSemialgebraic (coordinateProjection S) from H τ S hS
  intro τ instτ
  suffices Hτ : ∀ [Finite τ], ∀ (S : Set ((σ ⊕ τ) → ℝ)),
      IsSemialgebraic S → IsSemialgebraic (coordinateProjection S) from Hτ
  apply Finite.induction_empty_option
    (P := fun τ => ∀ [Finite τ], ∀ (S : Set ((σ ⊕ τ) → ℝ)),
      IsSemialgebraic S → IsSemialgebraic (coordinateProjection S))
  · intro α β e ih instβ S hS
    letI : Finite α := Finite.of_equiv β e.symm
    let r : σ ⊕ β → σ ⊕ α := Sum.map id e.symm
    have hT := hS.reindex r
    have h := ih {v : σ ⊕ α → ℝ | (fun j => v (r j)) ∈ S} hT
    convert h using 1
    ext x
    change (∃ y : β → ℝ, Sum.elim x y ∈ S) ↔
      ∃ y : α → ℝ, (fun j => Sum.elim x y (r j)) ∈ S
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fun a => y (e a), ?_⟩
      convert hy using 1
      funext j
      cases j <;> simp [r]
    · rintro ⟨y, hy⟩
      refine ⟨fun b => y (e.symm b), ?_⟩
      convert hy using 1
      funext j
      cases j <;> rfl
  · intro _ S hS
    have h := hS.reindex (fun j : σ ⊕ PEmpty => Sum.elim id PEmpty.elim j)
    convert h using 1
    ext x
    change (∃ y : PEmpty → ℝ, Sum.elim x y ∈ S) ↔ _
    constructor
    · rintro ⟨y, hy⟩
      change (fun i => x (Sum.elim id PEmpty.elim i)) ∈ S
      convert hy using 1
      funext j
      rcases j with i | j
      · rfl
      · exact j.elim
    · intro hx
      change (fun i => x (Sum.elim id PEmpty.elim i)) ∈ S at hx
      refine ⟨PEmpty.elim, ?_⟩
      convert hx using 1
      funext j
      rcases j with i | j
      · rfl
      · exact j.elim
  · intro α _ ih _ S hS
    have hT := hS.reindex (optionProjectionReindex (σ := σ) (τ := α))
    have hU := hT.scalar_projection
    have h := ih {v : σ ⊕ α → ℝ | ∃ t : ℝ,
      (fun j => Option.elim (optionProjectionReindex j) t v) ∈ S} hU
    convert h using 1
    ext x
    change (∃ y : Option α → ℝ, Sum.elim x y ∈ S) ↔
      ∃ y : α → ℝ, ∃ t : ℝ,
        (fun j => Option.elim (optionProjectionReindex j) t (Sum.elim x y)) ∈ S
    simp only [optionProjectionReindex_eval]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fun a => y (some a), y none, ?_⟩
      convert hy using 1
      funext j
      rcases j with i | (_ | j) <;> rfl
    · rintro ⟨y, t, hy⟩
      exact ⟨fun j => Option.elim j t y, hy⟩

end RealAlgebraicGeometry
end BfgsVerification
