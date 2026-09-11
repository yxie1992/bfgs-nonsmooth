import BfgsVerification.SmoothComponentTargets
set_option pp.universes true
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_subset
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_subset
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_eq_of_path
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_eq_of_path
#check BfgsVerification.RealAlgebraicGeometry.PiecewiseSmoothPath.prefix
#print axioms BfgsVerification.RealAlgebraicGeometry.PiecewiseSmoothPath.prefix
#check BfgsVerification.RealAlgebraicGeometry.PiecewiseSmoothPath.in_component
#print axioms BfgsVerification.RealAlgebraicGeometry.PiecewiseSmoothPath.in_component
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_piecewiseSmoothConnected
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_piecewiseSmoothConnected
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_eq_union_cover
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_eq_union_cover
#check BfgsVerification.RealAlgebraicGeometry.finite_smooth_components_of_finite_smooth_cover
#print axioms BfgsVerification.RealAlgebraicGeometry.finite_smooth_components_of_finite_smooth_cover
#check BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_semialgebraic_of_finite_smooth_cover
#print axioms BfgsVerification.RealAlgebraicGeometry.piecewiseSmoothComponent_semialgebraic_of_finite_smooth_cover
#check BfgsVerification.RealAlgebraicGeometry.finite_semialgebraic_smooth_components
#print axioms BfgsVerification.RealAlgebraicGeometry.finite_semialgebraic_smooth_components
#check BfgsVerification.FiniteSmoothComponentsTarget
#print axioms BfgsVerification.FiniteSmoothComponentsTarget
#check BfgsVerification.finiteSmoothComponents
#print axioms BfgsVerification.finiteSmoothComponents

open Set BfgsVerification BfgsVerification.RealAlgebraicGeometry
noncomputable section
namespace SmoothComponentIndependentReview
def CompleteContract : Prop := ∀ {σ : Type} [Fintype σ]
    {m : ℕ} {S : Set (σ → ℝ)} (C : Fin m → Set (σ → ℝ)),
    S = ⋃ i, C i →
    (∀ i, IsSemialgebraic (C i) ∧ PiecewiseSmoothConnected (C i)) →
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x)
open Lean Elab Command in
run_cmd do
  for d in [`BfgsVerification.RealAlgebraicGeometry.finite_semialgebraic_smooth_components,
      `BfgsVerification.finiteSmoothComponents] do
    let sameType ← liftTermElabM do
      let e ← Meta.mkConstWithFreshMVarLevels d
      let ty ← Meta.inferType e
      Meta.isDefEq ty (mkConst `SmoothComponentIndependentReview.CompleteContract)
    unless sameType do throwError "independent actual smooth-component contract mismatch"
    logInfo m!"SMOOTH_COMPONENT_PEER_EXACT_OK {d}"
end SmoothComponentIndependentReview
