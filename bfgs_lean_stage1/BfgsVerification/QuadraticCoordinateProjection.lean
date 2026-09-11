import BfgsVerification.SemialgebraicQuadraticProjection
import BfgsVerification.SemialgebraicSupportProjection

/-! Literal multivariate polynomial sets and their actual coordinate images.
The input polynomial has arbitrary polynomial parameter coefficients. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*}

def quadraticPolynomial (a b c : MvPolynomial σ ℝ) : MvPolynomial (σ ⊕ Unit) ℝ :=
  MvPolynomial.rename Sum.inl a * (X (.inr ()))^2 +
    MvPolynomial.rename Sum.inl b * X (.inr ()) + MvPolynomial.rename Sum.inl c

theorem quadraticPolynomial_eval (a b c : MvPolynomial σ ℝ) (x : σ → ℝ) (t : ℝ) :
    MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) (quadraticPolynomial a b c) =
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t := by
  simp [quadraticPolynomial,quadraticValue,MvPolynomial.eval_rename,Function.comp_def]

theorem quadratic_coordinate_projection_iff (a b c : MvPolynomial σ ℝ)
    (P : ℝ → Prop) (x : σ → ℝ) :
    x ∈ coordinateProjection {v : (σ ⊕ Unit) → ℝ |
      P (MvPolynomial.eval v (quadraticPolynomial a b c))} ↔
      ∃ t : ℝ, P (quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t) := by
  change (∃ y : Unit → ℝ, P (MvPolynomial.eval (Sum.elim x y) _)) ↔ _
  constructor
  · rintro ⟨y,hy⟩
    have he : y=(fun _ : Unit => y ()) := by funext i; cases i; rfl
    rw [he,quadraticPolynomial_eval] at hy
    exact ⟨y (),hy⟩
  · rintro ⟨t,ht⟩
    exact ⟨fun _ => t,by rwa [quadraticPolynomial_eval]⟩

theorem quadratic_coordinate_projections_semialgebraic [Finite σ] (a b c : MvPolynomial σ ℝ) :
    IsSemialgebraic (coordinateProjection {v : (σ ⊕ Unit) → ℝ |
      MvPolynomial.eval v (quadraticPolynomial a b c)=0}) ∧
    IsSemialgebraic (coordinateProjection {v : (σ ⊕ Unit) → ℝ |
      0<MvPolynomial.eval v (quadraticPolynomial a b c)}) ∧
    IsSemialgebraic (coordinateProjection {v : (σ ⊕ Unit) → ℝ |
      0≤MvPolynomial.eval v (quadraticPolynomial a b c)}) := by
  have h0 := quadratic_zero_projection_semialgebraic a b c
  have hp := quadratic_positive_projection_semialgebraic a b c
  have hn := quadratic_nonnegative_projection_semialgebraic a b c
  constructor
  · convert h0 using 1
    ext x
    exact quadratic_coordinate_projection_iff a b c (·=0) x
  · constructor
    · convert hp using 1
      ext x
      exact quadratic_coordinate_projection_iff a b c (0<·) x
    · convert hn using 1
      ext x
      exact quadratic_coordinate_projection_iff a b c (0≤·) x

end RealAlgebraicGeometry
end BfgsVerification
