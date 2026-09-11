import BfgsVerification.SimultaneousSignProjection
import Mathlib.Data.Fintype.Option

/-! Arbitrary finite Boolean polynomial formulas are projected by enumerating
simultaneous sign patterns, retaining a single common scalar witness. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*}

def PolynomialFormula.atomPolynomials : PolynomialFormula σ → Finset (MvPolynomial σ ℝ) := by
  classical
  exact fun
  | .equalZero p => {p}
  | .positive p => {p}
  | .and f g => f.atomPolynomials ∪ g.atomPolynomials
  | .not f => f.atomPolynomials

def PolynomialFormula.signHolds : PolynomialFormula σ → (MvPolynomial σ ℝ → SignType) → Prop
  | .equalZero p, s => s p = 0
  | .positive p, s => s p = 1
  | .and f g, s => f.signHolds s ∧ g.signHolds s
  | .not f, s => ¬f.signHolds s

theorem PolynomialFormula.holds_iff_signHolds (f : PolynomialFormula σ) (x : σ → ℝ) :
    f.Holds x ↔ f.signHolds (fun p => SignType.sign (MvPolynomial.eval x p)) := by
  induction f with
  | equalZero p => exact sign_eq_zero_iff.symm
  | positive p => exact sign_eq_one_iff.symm
  | and f g hf hg => exact and_congr hf hg
  | not f hf => exact not_congr hf

theorem PolynomialFormula.signHolds_congr (f : PolynomialFormula σ)
    {s t : MvPolynomial σ ℝ → SignType}
    (h : ∀ p ∈ f.atomPolynomials, s p = t p) : f.signHolds s ↔ f.signHolds t := by
  classical
  induction f with
  | equalZero p => simp only [signHolds, h p (Finset.mem_singleton_self p)]
  | positive p => simp only [signHolds, h p (Finset.mem_singleton_self p)]
  | and f g hf hg =>
    exact and_congr (hf (fun p hp => h p (Finset.mem_union_left _ hp)))
      (hg (fun p hp => h p (Finset.mem_union_right _ hp)))
  | not f hf => exact not_congr (hf h)

def PolynomialFormula.extendSigns (f : PolynomialFormula σ)
    (s : f.atomPolynomials → SignType) : MvPolynomial σ ℝ → SignType := by
  classical
  exact fun p => if hp : p ∈ f.atomPolynomials then s ⟨p, hp⟩ else 0

theorem PolynomialFormula.holds_iff_finite_sign_pattern
    (f : PolynomialFormula σ) (x : σ → ℝ) :
    f.Holds x ↔ ∃ s : f.atomPolynomials → SignType,
      f.signHolds (f.extendSigns s) ∧
        ∀ p : f.atomPolynomials, SignType.sign (MvPolynomial.eval x p.val) = s p := by
  classical
  rw [f.holds_iff_signHolds]
  constructor
  · intro hx
    refine ⟨(fun p => SignType.sign (MvPolynomial.eval x p.val)), ?_, fun _ => rfl⟩
    apply (f.signHolds_congr ?_).mp hx
    intro p hp
    simp only [extendSigns, dif_pos hp]
  · rintro ⟨s, hs, he⟩
    apply (f.signHolds_congr ?_).mpr hs
    intro p hp
    simpa only [extendSigns, dif_pos hp] using he ⟨p, hp⟩

theorem polynomial_simultaneous_sign_projection_finite
    [Finite σ] {ι : Type*} [Fintype ι]
    (q : ι → MvPolynomial (Option σ) ℝ) (ω : ι → SignType) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, SignType.sign (MvPolynomial.eval (fun j => Option.elim j t x) (q i)) = ω i} := by
  classical
  let e := Fintype.equivFin ι
  have h := polynomial_simultaneous_sign_projection (fun i => q (e.symm i))
    (fun i => ω (e.symm i))
  convert h using 1
  ext x
  apply exists_congr
  intro t
  constructor
  · intro h i
    exact h _
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (e i)

theorem polynomial_boolean_scalar_projection [Finite σ]
    (f : PolynomialFormula (Option σ)) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      f.Holds (fun j => Option.elim j t x)} := by
  classical
  let I := f.atomPolynomials
  let S : (I → SignType) → Set (σ → ℝ) := fun s =>
    {x | ∃ t : ℝ, ∀ p : I,
      SignType.sign (MvPolynomial.eval (fun j => Option.elim j t x) p.val) = s p}
  have hS : ∀ s, IsSemialgebraic (S s) := fun s =>
    polynomial_simultaneous_sign_projection_finite (fun p : I => p.val) s
  have h := isSemialgebraic_finset_union
    (Finset.univ.filter (fun s : I → SignType => f.signHolds (f.extendSigns s))) S
    (fun s _ => hS s)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    S, f.holds_iff_finite_sign_pattern]
  constructor
  · rintro ⟨t, s, hs, he⟩
    exact ⟨s, hs, t, he⟩
  · rintro ⟨s, hs, t, he⟩
    exact ⟨t, s, hs, he⟩

theorem IsSemialgebraic.scalar_projection [Fintype σ]
    {S : Set (Option σ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      (fun j => Option.elim j t x) ∈ S} := by
  obtain ⟨f, hf⟩ := hS
  simpa only [hf] using polynomial_boolean_scalar_projection f

end RealAlgebraicGeometry
end BfgsVerification
