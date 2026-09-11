import BfgsVerification.LScalarTargets

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.lScalarRamp
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarRampTarget)
  unless ok do throwError "target mismatch: lScalarRamp"
  logInfo "EXACT_TARGET_OK lScalarRamp LScalarRampTarget"
  let info ← getConstInfo `BfgsVerification.lScalarDefinition
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarDefinitionTarget)
  unless ok do throwError "target mismatch: lScalarDefinition"
  logInfo "EXACT_TARGET_OK lScalarDefinition LScalarDefinitionTarget"
  let info ← getConstInfo `BfgsVerification.lScalarRegularity
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarRegularityTarget)
  unless ok do throwError "target mismatch: lScalarRegularity"
  logInfo "EXACT_TARGET_OK lScalarRegularity LScalarRegularityTarget"
  let info ← getConstInfo `BfgsVerification.lScalarNodes
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarNodeTarget)
  unless ok do throwError "target mismatch: lScalarNodes"
  logInfo "EXACT_TARGET_OK lScalarNodes LScalarNodeTarget"
  let info ← getConstInfo `BfgsVerification.lScalarPeaks
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LScalarPeaksTarget)
  unless ok do throwError "target mismatch: lScalarPeaks"
  logInfo "EXACT_TARGET_OK lScalarPeaks LScalarPeaksTarget"
