import BfgsVerification.PiecewiseSmoothComponents

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem finite_semialgebraic_smooth_components {σ : Type*} [Fintype σ]
    {m : ℕ} {S : Set (σ → ℝ)} (C : Fin m → Set (σ → ℝ))
    (hcover : S = ⋃ i, C i)
    (hC : ∀ i, IsSemialgebraic (C i) ∧ PiecewiseSmoothConnected (C i)) :
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x) :=
  ⟨finite_smooth_components_of_finite_smooth_cover C hcover (fun i => (hC i).2),
    fun x => ⟨piecewiseSmoothComponent_semialgebraic_of_finite_smooth_cover C hcover
      (fun i => (hC i).2) (fun i => (hC i).1) x,
      piecewiseSmoothComponent_piecewiseSmoothConnected S x⟩⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def FiniteSmoothComponentsTarget : Prop := ∀ {σ : Type} [Fintype σ]
    {m : ℕ} {S : Set (σ → ℝ)} (C : Fin m → Set (σ → ℝ)),
    S = ⋃ i, C i →
    (∀ i, IsSemialgebraic (C i) ∧ PiecewiseSmoothConnected (C i)) →
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x)

theorem finiteSmoothComponents : FiniteSmoothComponentsTarget :=
  finite_semialgebraic_smooth_components

end BfgsVerification
