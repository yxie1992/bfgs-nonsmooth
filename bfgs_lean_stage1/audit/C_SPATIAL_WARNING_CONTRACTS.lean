import BfgsVerification.SpatialQuadraticTargets
open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.spatialCanonicalWarning, `BfgsVerification.SpatialCanonicalWarningTarget),
    (`BfgsVerification.spatialQuadraticRadial, `BfgsVerification.SpatialQuadraticRadialTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
