import BfgsVerification.FixedNormalCompositeEndToEnd

#print BfgsVerification.TangentialCompositeConvergenceTarget
#check @BfgsVerification.tangentialCompositeConvergence
example : BfgsVerification.TangentialCompositeConvergenceTarget := BfgsVerification.tangentialCompositeConvergence

#print BfgsVerification.TangentialCompositeLocalBasinTarget
#check @BfgsVerification.tangentialCompositeLocalBasin
example : BfgsVerification.TangentialCompositeLocalBasinTarget := BfgsVerification.tangentialCompositeLocalBasin

#print BfgsVerification.StrongCompositeConvergenceTarget
#check @BfgsVerification.strongCompositeConvergence
example : BfgsVerification.StrongCompositeConvergenceTarget := BfgsVerification.strongCompositeConvergence

#print BfgsVerification.StrongCompositeLocalBasinTarget
#check @BfgsVerification.strongCompositeLocalBasin
example : BfgsVerification.StrongCompositeLocalBasinTarget := BfgsVerification.strongCompositeLocalBasin

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.tangentialCompositeConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.TangentialCompositeConvergenceTarget)
  unless ok do throwError "exact target mismatch: tangentialCompositeConvergence"
  logInfo "EXACT_TARGET_OK tangentialCompositeConvergence TangentialCompositeConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.tangentialCompositeLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.TangentialCompositeLocalBasinTarget)
  unless ok do throwError "exact target mismatch: tangentialCompositeLocalBasin"
  logInfo "EXACT_TARGET_OK tangentialCompositeLocalBasin TangentialCompositeLocalBasinTarget"
  let info ← getConstInfo `BfgsVerification.strongCompositeConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.StrongCompositeConvergenceTarget)
  unless ok do throwError "exact target mismatch: strongCompositeConvergence"
  logInfo "EXACT_TARGET_OK strongCompositeConvergence StrongCompositeConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.strongCompositeLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.StrongCompositeLocalBasinTarget)
  unless ok do throwError "exact target mismatch: strongCompositeLocalBasin"
  logInfo "EXACT_TARGET_OK strongCompositeLocalBasin StrongCompositeLocalBasinTarget"
