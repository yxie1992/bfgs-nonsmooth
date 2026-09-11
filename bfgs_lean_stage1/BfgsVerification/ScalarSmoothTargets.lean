import BfgsVerification.SemialgebraicScalarSmooth

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
open RealAlgebraicGeometry

def SemialgebraicFunctionPiecesTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (D : Set (Vec n)),
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ D ∧ v none = F (fun i => v (some i))} →
    ∃ C : Finset (Set (Vec n)),
      (∀ S ∈ C, IsSemialgebraic S ∧ ContDiffOn ℝ ∞ F S) ∧ ⋃ S ∈ C, S = D

theorem semialgebraicFunctionPieces : SemialgebraicFunctionPiecesTarget := by
  intro n F D hf
  exact semialgebraic_function_finite_smooth_pieces hf

def SemialgebraicScalarSmoothTarget : Prop :=
  ∀ (f : ℝ → ℝ) (D : Set ℝ),
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ D ∧ v none = f (v (some 0))} →
    ∃ E : Finset ℝ, ∀ t ∈ D, t ∉ E → ContDiffAt ℝ ∞ f t

theorem semialgebraicScalarSmooth : SemialgebraicScalarSmoothTarget := by
  intro f D hf
  exact semialgebraic_scalar_smooth_except_finite hf

def SemialgebraicIntervalSmoothTarget : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), ContinuousOn f (Icc a b) →
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ Icc a b ∧ v none = f (v (some 0))} →
    ∃ E : Finset ℝ, ContinuousOn f (Icc a b) ∧
      ∀ t ∈ Ioo a b, t ∉ E → ContDiffAt ℝ ∞ f t

theorem semialgebraicIntervalSmooth : SemialgebraicIntervalSmoothTarget := by
  intro f a b hc hf
  exact continuous_semialgebraic_interval_piecewise_smooth hc hf

end BfgsVerification
