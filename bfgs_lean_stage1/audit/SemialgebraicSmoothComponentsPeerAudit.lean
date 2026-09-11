import BfgsVerification.SemialgebraicSmoothComponents
set_option pp.universes true
#check BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components
#check BfgsVerification.SemialgebraicSmoothComponentsTarget
#print axioms BfgsVerification.SemialgebraicSmoothComponentsTarget
#check BfgsVerification.semialgebraicSmoothComponents
#print axioms BfgsVerification.semialgebraicSmoothComponents

noncomputable section
open Set BfgsVerification BfgsVerification.RealAlgebraicGeometry
namespace ActualSmoothComponentIndependentReview
def CompleteContract : Prop := ∀ {σ : Type} [Fintype σ]
    {S : Set (σ → ℝ)}, IsSemialgebraic S →
    (piecewiseSmoothComponent S '' S).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent S x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent S x)
open Lean Elab Command in
run_cmd do
  for d in [`BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components,
      `BfgsVerification.semialgebraicSmoothComponents] do
    let sameType ← liftTermElabM do
      let e ← Meta.mkConstWithFreshMVarLevels d
      let ty ← Meta.inferType e
      Meta.isDefEq ty (mkConst `ActualSmoothComponentIndependentReview.CompleteContract)
    unless sameType do throwError "independent unconditional actual smooth-component contract mismatch"
    logInfo m!"ACTUAL_SMOOTH_COMPONENT_PEER_EXACT_OK {d}"
end ActualSmoothComponentIndependentReview
