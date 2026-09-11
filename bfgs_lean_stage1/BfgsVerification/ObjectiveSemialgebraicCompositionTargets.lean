import BfgsVerification.SemialgebraicCurveSmooth

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
open RealAlgebraicGeometry

def ObjectiveSemialgebraicCompositionTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ), ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    ∀ p : ℝ → Vec n, ContinuousOn p (Icc 0 1) → IsSemialgebraicCurveOn p (Icc 0 1) →
    IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ Icc (0 : ℝ) 1 ∧ v none = (F ∘ p) (v (some 0))} ∧
    ContinuousOn (F ∘ p) (Icc 0 1) ∧
    ∃ E : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ E → ContDiffAt ℝ ∞ (F ∘ p) t

theorem objectiveSemialgebraicComposition : ObjectiveSemialgebraicCompositionTarget := by
  intro n F hconv hF p hc hp
  exact convex_semialgebraic_objective_curve_piecewise_smooth hconv hF hc hp

def SemialgebraicCurveSmoothTarget : Prop :=
  ∀ (σ : Type) [Fintype σ] (p : ℝ → σ → ℝ) (J : Set ℝ),
    IsSemialgebraicCurveOn p J →
    ∃ E : Finset ℝ, ∀ t ∈ J, t ∉ E → ContDiffAt ℝ ∞ p t

theorem semialgebraicCurveSmooth : SemialgebraicCurveSmoothTarget := by
  intro σ _ p J hp
  exact semialgebraic_curve_smooth_except_finite hp

end BfgsVerification
