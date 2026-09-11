import BfgsVerification.NormalSpikeExampleTargets

#print BfgsVerification.NormalSpike.SpikeObjectiveConvergenceTarget
#check @BfgsVerification.NormalSpike.spikeObjectiveConvergence
example : BfgsVerification.NormalSpike.SpikeObjectiveConvergenceTarget := BfgsVerification.NormalSpike.spikeObjectiveConvergence

#print BfgsVerification.NormalSpike.SpikeRadialSeparationTarget
#check @BfgsVerification.NormalSpike.spikeRadialSeparation
example : BfgsVerification.NormalSpike.SpikeRadialSeparationTarget := BfgsVerification.NormalSpike.spikeRadialSeparation

#print BfgsVerification.NormalSpike.SpikeObjectiveGeometryTarget
#check @BfgsVerification.NormalSpike.spikeObjectiveGeometry
example : BfgsVerification.NormalSpike.SpikeObjectiveGeometryTarget := BfgsVerification.NormalSpike.spikeObjectiveGeometry

#print BfgsVerification.NormalSpike.SpikeHessianPeakTarget
#check @BfgsVerification.NormalSpike.spikeHessianPeaks
example : BfgsVerification.NormalSpike.SpikeHessianPeakTarget := BfgsVerification.NormalSpike.spikeHessianPeaks

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.NormalSpike.spikeObjectiveConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.SpikeObjectiveConvergenceTarget)
  unless ok do throwError "exact target mismatch: spikeObjectiveConvergence"
  logInfo "EXACT_TARGET_OK spikeObjectiveConvergence SpikeObjectiveConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.spikeRadialSeparation
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.SpikeRadialSeparationTarget)
  unless ok do throwError "exact target mismatch: spikeRadialSeparation"
  logInfo "EXACT_TARGET_OK spikeRadialSeparation SpikeRadialSeparationTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.spikeObjectiveGeometry
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.SpikeObjectiveGeometryTarget)
  unless ok do throwError "exact target mismatch: spikeObjectiveGeometry"
  logInfo "EXACT_TARGET_OK spikeObjectiveGeometry SpikeObjectiveGeometryTarget"
  let info ← getConstInfo `BfgsVerification.NormalSpike.spikeHessianPeaks
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.SpikeHessianPeakTarget)
  unless ok do throwError "exact target mismatch: spikeHessianPeaks"
  logInfo "EXACT_TARGET_OK spikeHessianPeaks SpikeHessianPeakTarget"
