import BfgsVerification.LScalarStepTargets

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.lScalarStepDefinition
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarStepDefinitionTarget)
  unless ok do throwError "target mismatch: lScalarStepDefinition"
  logInfo "EXACT_TARGET_OK lScalarStepDefinition LScalarStepDefinitionTarget"
  let info ← getConstInfo `BfgsVerification.lScalarStepGeometry
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarStepGeometryTarget)
  unless ok do throwError "target mismatch: lScalarStepGeometry"
  logInfo "EXACT_TARGET_OK lScalarStepGeometry LScalarStepGeometryTarget"
  let info ← getConstInfo `BfgsVerification.lScalarStepNodes
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarStepNodeTarget)
  unless ok do throwError "target mismatch: lScalarStepNodes"
  logInfo "EXACT_TARGET_OK lScalarStepNodes LScalarStepNodeTarget"
  let info ← getConstInfo `BfgsVerification.lScalarStepLocal
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarStepLocalTarget)
  unless ok do throwError "target mismatch: lScalarStepLocal"
  logInfo "EXACT_TARGET_OK lScalarStepLocal LScalarStepLocalTarget"
