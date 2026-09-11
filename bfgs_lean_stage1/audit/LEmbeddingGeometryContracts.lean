import BfgsVerification.LEmbeddingGeometryTargets
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.LEmbedding.regularity
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LEmbedding.RegularityTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LEmbedding.regularity BfgsVerification.LEmbedding.RegularityTarget"
  let info ← getConstInfo `BfgsVerification.LEmbedding.origin
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LEmbedding.OriginTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LEmbedding.origin BfgsVerification.LEmbedding.OriginTarget"
  let info ← getConstInfo `BfgsVerification.LEmbedding.hessian
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LEmbedding.HessianTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LEmbedding.hessian BfgsVerification.LEmbedding.HessianTarget"
  let info ← getConstInfo `BfgsVerification.LEmbedding.localModel
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LEmbedding.LocalModelTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LEmbedding.localModel BfgsVerification.LEmbedding.LocalModelTarget"
