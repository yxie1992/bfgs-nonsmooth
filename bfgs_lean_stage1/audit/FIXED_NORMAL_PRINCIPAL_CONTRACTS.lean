import BfgsVerification.FixedNormalEndToEnd

#print BfgsVerification.FixedNormalHyperplaneTarget
#check @BfgsVerification.fixedNormalHyperplane
example : BfgsVerification.FixedNormalHyperplaneTarget := BfgsVerification.fixedNormalHyperplane

#print BfgsVerification.ParallelInterfacesClusterTarget
#check @BfgsVerification.parallelInterfacesCluster
example : BfgsVerification.ParallelInterfacesClusterTarget := BfgsVerification.parallelInterfacesCluster

#print BfgsVerification.ParallelInterfacesConvergenceTarget
#check @BfgsVerification.parallelInterfacesConvergence
example : BfgsVerification.ParallelInterfacesConvergenceTarget := BfgsVerification.parallelInterfacesConvergence

#print BfgsVerification.FixedNormalLocalBasinTarget
#check @BfgsVerification.fixedNormalLocalBasin
example : BfgsVerification.FixedNormalLocalBasinTarget := BfgsVerification.fixedNormalLocalBasin

#print BfgsVerification.ParallelInterfacesLocalBasinTarget
#check @BfgsVerification.parallelInterfacesLocalBasin
example : BfgsVerification.ParallelInterfacesLocalBasinTarget := BfgsVerification.parallelInterfacesLocalBasin

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let info ← getConstInfo `BfgsVerification.fixedNormalHyperplane
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.FixedNormalHyperplaneTarget)
  unless ok do throwError "exact target mismatch: fixedNormalHyperplane"
  logInfo "EXACT_TARGET_OK fixedNormalHyperplane FixedNormalHyperplaneTarget"
  let info ← getConstInfo `BfgsVerification.parallelInterfacesCluster
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.ParallelInterfacesClusterTarget)
  unless ok do throwError "exact target mismatch: parallelInterfacesCluster"
  logInfo "EXACT_TARGET_OK parallelInterfacesCluster ParallelInterfacesClusterTarget"
  let info ← getConstInfo `BfgsVerification.parallelInterfacesConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.ParallelInterfacesConvergenceTarget)
  unless ok do throwError "exact target mismatch: parallelInterfacesConvergence"
  logInfo "EXACT_TARGET_OK parallelInterfacesConvergence ParallelInterfacesConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.fixedNormalLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.FixedNormalLocalBasinTarget)
  unless ok do throwError "exact target mismatch: fixedNormalLocalBasin"
  logInfo "EXACT_TARGET_OK fixedNormalLocalBasin FixedNormalLocalBasinTarget"
  let info ← getConstInfo `BfgsVerification.parallelInterfacesLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.ParallelInterfacesLocalBasinTarget)
  unless ok do throwError "exact target mismatch: parallelInterfacesLocalBasin"
  logInfo "EXACT_TARGET_OK parallelInterfacesLocalBasin ParallelInterfacesLocalBasinTarget"
