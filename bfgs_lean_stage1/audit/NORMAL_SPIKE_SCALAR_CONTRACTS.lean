import BfgsVerification.NormalSpikeTargets
#print BfgsVerification.NormalSpike.SourceSpikePropertiesTarget
#check @BfgsVerification.NormalSpike.sourceSpikeProperties
example : BfgsVerification.NormalSpike.SourceSpikePropertiesTarget :=
  BfgsVerification.NormalSpike.sourceSpikeProperties
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.NormalSpike.sourceSpikeProperties
  let ok ← liftTermElabM <| Meta.isDefEq info.type
    (mkConst `BfgsVerification.NormalSpike.SourceSpikePropertiesTarget)
  unless ok do throwError "exact target mismatch: sourceSpikeProperties"
  logInfo "EXACT_TARGET_OK sourceSpikeProperties SourceSpikePropertiesTarget"
