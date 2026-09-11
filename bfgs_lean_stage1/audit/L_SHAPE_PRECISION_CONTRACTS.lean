import BfgsVerification.LShapePrecision
open Lean Elab Command in
run_cmd do
  let decl := `BfgsVerification.LShapePrecision.actualJacobianPrecision
  let target := `BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget
  let info ← getConstInfo decl
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
  unless ok do throwError "actual Jacobian precision contract mismatch"
  logInfo m!"EXACT_TARGET_OK {decl}"
