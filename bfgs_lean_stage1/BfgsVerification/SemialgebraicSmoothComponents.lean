import BfgsVerification.SmoothComponentTargets
import BfgsVerification.SemialgebraicSmoothCover
import Mathlib.Data.Fintype.EquivFin

/-! Actual smooth-path components of arbitrary genuine semialgebraic sets.
The finite smooth cover is derived by the checked dimension induction. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem semialgebraic_smooth_components {σ : Type*} [Fintype σ]
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x) := by
  classical
  obtain ⟨C, hC, hcover⟩ := semialgebraic_finite_smooth_cover hS
  let D : Fin C.card → Set (σ → ℝ) := fun i => (C.equivFin.symm i).val
  have hD : ∀ i, D i ∈ C := fun i => (C.equivFin.symm i).property
  have he : S = ⋃ i, D i := by
    rw [← hcover]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨T, hT, hx⟩
      refine ⟨C.equivFin ⟨T,hT⟩, ?_⟩
      simpa only [D, Equiv.symm_apply_apply] using hx
    · rintro ⟨i, hi⟩
      exact ⟨D i, hD i, hi⟩
  exact finite_semialgebraic_smooth_components D he (fun i => hC (D i) (hD i))

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def SemialgebraicSmoothComponentsTarget : Prop := ∀ {σ : Type} [Fintype σ]
    {S : Set (σ → ℝ)}, IsSemialgebraic S →
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x)

theorem semialgebraicSmoothComponents : SemialgebraicSmoothComponentsTarget :=
  semialgebraic_smooth_components

end BfgsVerification
