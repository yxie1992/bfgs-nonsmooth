import BfgsVerification.FiniteMaxHessianTargets
open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.finiteMaxTaylor, `BfgsVerification.FiniteMaxTaylorTarget),
    (`BfgsVerification.finiteMaxActualHessian, `BfgsVerification.FiniteMaxActualHessianTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
