import BfgsVerification.SemialgebraicCurveJoining
import BfgsVerification.SemialgebraicScalarGraphArithmetic

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Actual graph preservation for the operations used in path concatenation
and lifting. The parameter domain is the closed unit interval. -/
def SemialgebraicPathGraphOperationsTarget : Prop :=
  ∀ (n m : ℕ) (p q : ℝ → Vec n),
    IsSemialgebraicCurveOn p (Icc 0 1) → IsSemialgebraicCurveOn q (Icc 0 1) →
    IsSemialgebraicCurveOn (joinedCurve p q) (Icc 0 1) ∧
    IsSemialgebraicCurveOn (fun t => p (1-t)) (Icc 0 1) ∧
    ∀ (G : Vec n → Vec m) (S : Set (Vec n)), IsSemialgebraicMapOn G S →
      MapsTo p (Icc 0 1) S → IsSemialgebraicCurveOn (G ∘ p) (Icc 0 1)

theorem semialgebraicPathGraphOperations : SemialgebraicPathGraphOperationsTarget := by
  intro n m p q hp hq
  exact ⟨hp.joinedCurve hq,hp.symm,fun _ _ hG hpS => hp.map hG hpS⟩

/-- The actual scalar graph-lift and section arithmetic used by cylindrical
paths are derived by polynomial graph equations and genuine projection. -/
def SemialgebraicScalarGraphOperationsTarget : Prop :=
  ∀ (n : ℕ) (S : Set (Vec n)) (f g : Vec n → ℝ), IsSemialgebraic S →
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))} →
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = g (fun i => v (some i))} →
    IsSemialgebraicMapOn (fun x j => Option.elim j (f x) x) S ∧
    ∀ a b c : ℝ, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧
        v none = a * f (fun i => v (some i)) + b * g (fun i => v (some i)) + c}

theorem semialgebraicScalarGraphOperations : SemialgebraicScalarGraphOperationsTarget := by
  intro n S f g hS hf hg
  exact ⟨IsSemialgebraicMapOn.graph_lift hS hf,semialgebraic_scalar_graph_affine hf hg⟩

end RealAlgebraicGeometry
end BfgsVerification
