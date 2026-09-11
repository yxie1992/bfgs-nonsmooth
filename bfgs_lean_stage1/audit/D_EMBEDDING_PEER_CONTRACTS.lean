import BfgsVerification.ReportEmbeddingEndToEnd

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.DEmbedding.objectiveGeometry
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.DEmbedding.ObjectiveGeometryTarget)
  unless ok do throwError "target mismatch: BfgsVerification.DEmbedding.objectiveGeometry"
  logInfo "EXACT_TARGET_OK BfgsVerification.DEmbedding.objectiveGeometry BfgsVerification.DEmbedding.ObjectiveGeometryTarget"
  let info ← getConstInfo `BfgsVerification.DEmbedding.embeddingFailure
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.DEmbedding.EmbeddingFailureTarget)
  unless ok do throwError "target mismatch: BfgsVerification.DEmbedding.embeddingFailure"
  logInfo "EXACT_TARGET_OK BfgsVerification.DEmbedding.embeddingFailure BfgsVerification.DEmbedding.EmbeddingFailureTarget"
