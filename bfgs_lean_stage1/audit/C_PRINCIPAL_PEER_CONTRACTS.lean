import PlanarPrincipalEndToEnd

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.planarAffineCriticalCluster
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarAffineCriticalClusterTarget)
  unless ok do throwError "target mismatch: BfgsVerification.planarAffineCriticalCluster"
  logInfo "EXACT_TARGET_OK BfgsVerification.planarAffineCriticalCluster BfgsVerification.PlanarAffineCriticalClusterTarget"
  let info ← getConstInfo `BfgsVerification.planarConvergence
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarConvergenceTarget)
  unless ok do throwError "target mismatch: BfgsVerification.planarConvergence"
  logInfo "EXACT_TARGET_OK BfgsVerification.planarConvergence BfgsVerification.PlanarConvergenceTarget"
  let info ← getConstInfo `BfgsVerification.planarLocalBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarLocalBasinTarget)
  unless ok do throwError "target mismatch: BfgsVerification.planarLocalBasin"
  logInfo "EXACT_TARGET_OK BfgsVerification.planarLocalBasin BfgsVerification.PlanarLocalBasinTarget"
