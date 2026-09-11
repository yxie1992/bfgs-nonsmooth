import BfgsVerification.SemialgebraicPathComponents
import BfgsVerification.SemialgebraicPathCover
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem finite_semialgebraic_path_components_of_cover {σ : Type*} [Fintype σ]
    {m : ℕ} {S : Set (σ → ℝ)} (C : Fin m → Set (σ → ℝ))
    (hcover : S = ⋃ i, C i)
    (hC : ∀ i, IsSemialgebraic (C i) ∧ SemialgebraicPiecewiseSmoothConnected (C i)) :
    (semialgebraicSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (semialgebraicSmoothComponent S x) ∧
      SemialgebraicPiecewiseSmoothConnected (semialgebraicSmoothComponent S x) :=
  ⟨finite_semialgebraic_path_components_of_finite_path_cover C hcover (fun i => (hC i).2),
    fun x => ⟨semialgebraicSmoothComponent_semialgebraic_of_finite_path_cover C hcover
      (fun i => (hC i).2) (fun i => (hC i).1) x,
      semialgebraicSmoothComponent_connected S x⟩⟩

/-- Actual semialgebraic path classes, with no assumed finite cover or path oracle. -/
theorem semialgebraic_actual_path_components {σ : Type*} [Fintype σ]
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    (semialgebraicSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (semialgebraicSmoothComponent S x) ∧
      SemialgebraicPiecewiseSmoothConnected (semialgebraicSmoothComponent S x) := by
  classical
  obtain ⟨C, hC, hcover⟩ := semialgebraic_finite_path_cover hS
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
  exact finite_semialgebraic_path_components_of_cover D he (fun i => hC (D i) (hD i))

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def SemialgebraicActualPathComponentsTarget : Prop := ∀ {σ : Type} [Fintype σ]
    {S : Set (σ → ℝ)}, IsSemialgebraic S →
    (semialgebraicSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (semialgebraicSmoothComponent S x) ∧
      SemialgebraicPiecewiseSmoothConnected (semialgebraicSmoothComponent S x)

theorem semialgebraicActualPathComponents : SemialgebraicActualPathComponentsTarget :=
  semialgebraic_actual_path_components

end BfgsVerification
