import BfgsVerification.SemialgebraicSupportProjection
open Set BfgsVerification BfgsVerification.RealAlgebraicGeometry

def LiftedViolationContract : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
  IsSemialgebraicObjective F → IsSemialgebraic (badSupportSet F)

def ActualSupportProjectionContract : Prop := ∀ {n : ℕ} (F : Vec n → ℝ),
  (supportGraph F)ᶜ = coordinateProjection (badSupportSet F)

def ConditionalSupportingGraphContract : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
  IsSemialgebraicObjective F →
  (∀ S : Set (SupportAll n → ℝ), IsSemialgebraic S → IsSemialgebraic (coordinateProjection S)) →
  IsSemialgebraic (supportGraph F)

open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.RealAlgebraicGeometry.badSupportSet_semialgebraic, `LiftedViolationContract),
    (`BfgsVerification.RealAlgebraicGeometry.nonSupportGraph_eq_projection, `ActualSupportProjectionContract),
    (`BfgsVerification.RealAlgebraicGeometry.supportGraph_semialgebraic_of_projection, `ConditionalSupportingGraphContract)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_INFRASTRUCTURE_CONTRACT_OK {decl}"
