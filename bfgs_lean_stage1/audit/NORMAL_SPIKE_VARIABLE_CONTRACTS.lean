import BfgsVerification.NormalSpikeVariableTargets

#print BfgsVerification.NormalSpike.VariableSpikeConvergenceTarget
#check @BfgsVerification.NormalSpike.variableSpikeConvergence
example : BfgsVerification.NormalSpike.VariableSpikeConvergenceTarget := BfgsVerification.NormalSpike.variableSpikeConvergence

#print BfgsVerification.NormalSpike.VariableSpikeSeparationTarget
#check @BfgsVerification.NormalSpike.variableSpikeSeparation
example : BfgsVerification.NormalSpike.VariableSpikeSeparationTarget := BfgsVerification.NormalSpike.variableSpikeSeparation

#print BfgsVerification.NormalSpike.VariableSpikeNonsplittingTarget
#check @BfgsVerification.NormalSpike.variableSpikeNonsplitting
example : BfgsVerification.NormalSpike.VariableSpikeNonsplittingTarget := BfgsVerification.NormalSpike.variableSpikeNonsplitting

#print BfgsVerification.NormalSpike.VariableSpikeGeometryTarget
#check @BfgsVerification.NormalSpike.variableSpikeGeometry
example : BfgsVerification.NormalSpike.VariableSpikeGeometryTarget := BfgsVerification.NormalSpike.variableSpikeGeometry

#print BfgsVerification.NormalSpike.VariableSpikeHessianTarget
#check @BfgsVerification.NormalSpike.variableSpikeHessian
example : BfgsVerification.NormalSpike.VariableSpikeHessianTarget := BfgsVerification.NormalSpike.variableSpikeHessian

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.NormalSpike.variableSpikeConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.VariableSpikeConvergenceTarget)
  unless ok do throwError "exact target mismatch: variableSpikeConvergence"
  logInfo "EXACT_TARGET_OK variableSpikeConvergence VariableSpikeConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.variableSpikeSeparation
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.VariableSpikeSeparationTarget)
  unless ok do throwError "exact target mismatch: variableSpikeSeparation"
  logInfo "EXACT_TARGET_OK variableSpikeSeparation VariableSpikeSeparationTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.variableSpikeNonsplitting
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.VariableSpikeNonsplittingTarget)
  unless ok do throwError "exact target mismatch: variableSpikeNonsplitting"
  logInfo "EXACT_TARGET_OK variableSpikeNonsplitting VariableSpikeNonsplittingTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.variableSpikeGeometry
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.VariableSpikeGeometryTarget)
  unless ok do throwError "exact target mismatch: variableSpikeGeometry"
  logInfo "EXACT_TARGET_OK variableSpikeGeometry VariableSpikeGeometryTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.variableSpikeHessian
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.VariableSpikeHessianTarget)
  unless ok do throwError "exact target mismatch: variableSpikeHessian"
  logInfo "EXACT_TARGET_OK variableSpikeHessian VariableSpikeHessianTarget"
