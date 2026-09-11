import BfgsVerification.SemialgebraicSmoothBands
import BfgsVerification.OrderedGapConnectivity

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ] {r : ℕ}

theorem orderedGapCell_semialgebraicPiecewiseSmoothConnected
    (S : Set (σ → ℝ)) (f : Fin r → (σ → ℝ) → ℝ)
    (hSsa : IsSemialgebraic S) (hS : SemialgebraicPiecewiseSmoothConnected S)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x))
    (hgraph : ∀ i, IsSemialgebraic {v : Option σ → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))})
    (j : Fin (r+1)) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      ((fun k => v (some k)), v none) ∈ orderedGapCell S f j} := by
  by_cases hr : r = 0
  · subst r
    rw [orderedGapCell_empty]
    exact hS.full_cylinder hSsa
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  by_cases hj0 : j.val = 0
  · rw [orderedGapCell_bottom S f hf hrp j hj0]
    exact hS.lower_band hSsa (hsm _) (hgraph _)
  by_cases hjr : j.val = r
  · rw [orderedGapCell_top S f hf hrp j hjr]
    exact hS.upper_band hSsa (hsm _) (hgraph _)
  have hjp : 0 < j.val := Nat.pos_of_ne_zero hj0
  have hjlt : j.val < r := by have := j.isLt; omega
  rw [orderedGapCell_middle S f hf j hjp hjlt]
  apply hS.open_band hSsa (hsm _) (hsm _) (hgraph _) (hgraph _)
  intro x hx
  apply hf x hx
  change j.val-1 < j.val
  omega

theorem orderedCylindricalCell_semialgebraicPiecewiseSmoothConnected
    (S : Set (σ → ℝ)) (f : Fin r → (σ → ℝ) → ℝ)
    (hSsa : IsSemialgebraic S) (hS : SemialgebraicPiecewiseSmoothConnected S)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x))
    (hgraph : ∀ i, IsSemialgebraic {v : Option σ → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))})
    (i : Fin r ⊕ Fin (r+1)) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      ((fun k => v (some k)), v none) ∈ orderedCylindricalCell S f i} := by
  rcases i with i | j
  · exact hS.graph hSsa (hsm i) (hgraph i)
  · exact orderedGapCell_semialgebraicPiecewiseSmoothConnected S f hSsa hS hsm hf hgraph j

end RealAlgebraicGeometry
end BfgsVerification
