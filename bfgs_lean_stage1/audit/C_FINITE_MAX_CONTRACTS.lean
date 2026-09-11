import BfgsVerification.PlanarFiniteMaxTargets
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.planarFiniteMaxLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarFiniteMaxLocalBasinTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK planarFiniteMaxLocalBasin PlanarFiniteMaxLocalBasinTarget"
  let info ← getConstInfo `BfgsVerification.planarFiniteMaxHessianBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarFiniteMaxHessianBasinTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK planarFiniteMaxHessianBasin PlanarFiniteMaxHessianBasinTarget"
