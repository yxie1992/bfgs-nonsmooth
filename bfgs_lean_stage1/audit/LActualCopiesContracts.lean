import BfgsVerification.LActualCopyTargets
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.LActualCopies.smoothFailure
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LActualCopies.SmoothFailureTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LActualCopies.smoothFailure BfgsVerification.LActualCopies.SmoothFailureTarget"
  let info ← getConstInfo `BfgsVerification.LActualCopies.stepFailure
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LActualCopies.StepFailureTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LActualCopies.stepFailure BfgsVerification.LActualCopies.StepFailureTarget"
