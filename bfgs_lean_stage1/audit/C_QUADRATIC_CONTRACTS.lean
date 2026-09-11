import BfgsVerification.PlanarQuadraticTargets

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.planarQuadraticModel
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarQuadraticModelTarget)
  unless ok do throwError "target mismatch: planarQuadraticModel"
  logInfo "EXACT_TARGET_OK planarQuadraticModel PlanarQuadraticModelTarget"
  let info ← getConstInfo `BfgsVerification.planarQuadraticCoefficients
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarQuadraticCoefficientsTarget)
  unless ok do throwError "target mismatch: planarQuadraticCoefficients"
  logInfo "EXACT_TARGET_OK planarQuadraticCoefficients PlanarQuadraticCoefficientsTarget"
  let info ← getConstInfo `BfgsVerification.planarQuadraticBasin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarQuadraticBasinTarget)
  unless ok do throwError "target mismatch: planarQuadraticBasin"
  logInfo "EXACT_TARGET_OK planarQuadraticBasin PlanarQuadraticBasinTarget"
  let info ← getConstInfo `BfgsVerification.planarQuadraticCurve
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarQuadraticCurveTarget)
  unless ok do throwError "target mismatch: planarQuadraticCurve"
  logInfo "EXACT_TARGET_OK planarQuadraticCurve PlanarQuadraticCurveTarget"
  let info ← getConstInfo `BfgsVerification.planarQuadraticSeparation
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PlanarQuadraticSeparationTarget)
  unless ok do throwError "target mismatch: planarQuadraticSeparation"
  logInfo "EXACT_TARGET_OK planarQuadraticSeparation PlanarQuadraticSeparationTarget"
