import BfgsVerification.RectangularNuclearTargets

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.rectangularNuclearNorm
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.RectangularNuclearNormTarget)
  unless ok do throwError "target mismatch: rectangularNuclearNorm"
  logInfo "EXACT_TARGET_OK rectangularNuclearNorm RectangularNuclearNormTarget"
  let info ← getConstInfo `BfgsVerification.centeredRectangularNuclear
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.CenteredRectangularNuclearTarget)
  unless ok do throwError "target mismatch: centeredRectangularNuclear"
  logInfo "EXACT_TARGET_OK centeredRectangularNuclear CenteredRectangularNuclearTarget"
  let info ← getConstInfo `BfgsVerification.mixedNuclearPowers
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.MixedNuclearPowersTarget)
  unless ok do throwError "target mismatch: mixedNuclearPowers"
  logInfo "EXACT_TARGET_OK mixedNuclearPowers MixedNuclearPowersTarget"
  let info ← getConstInfo `BfgsVerification.firstDifferenceBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.FirstDifferenceBasinTarget)
  unless ok do throwError "target mismatch: firstDifferenceBasin"
  logInfo "EXACT_TARGET_OK firstDifferenceBasin FirstDifferenceBasinTarget"
