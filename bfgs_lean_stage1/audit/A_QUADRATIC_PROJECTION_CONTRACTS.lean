import BfgsVerification.QuadraticProjectionTargets
open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.realQuadraticElimination, `BfgsVerification.RealQuadraticEliminationTarget),
    (`BfgsVerification.quadraticPolynomialProjection, `BfgsVerification.QuadraticPolynomialProjectionTarget),
    (`BfgsVerification.quadraticUniversalConditions, `BfgsVerification.QuadraticUniversalConditionsTarget),
    (`BfgsVerification.actualDegreeTwoProjection, `BfgsVerification.ActualDegreeTwoProjectionTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
