import BfgsVerification.StableOrbitTargets
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.LocalStableOrbit.stableOrbit
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LocalStableOrbit.StableOrbitTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LocalStableOrbit.stableOrbit BfgsVerification.LocalStableOrbit.StableOrbitTarget"
  let info ← getConstInfo `BfgsVerification.LocalStableOrbit.positiveStableOrbit
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LocalStableOrbit.PositiveStableOrbitTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LocalStableOrbit.positiveStableOrbit BfgsVerification.LocalStableOrbit.PositiveStableOrbitTarget"
