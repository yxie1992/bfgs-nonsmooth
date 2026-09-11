import BfgsVerification.LStepEmbeddingTargets

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.lStepEmbeddingGeometry
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LStepEmbeddingGeometryTarget)
  unless ok do throwError "target mismatch: lStepEmbeddingGeometry"
  logInfo "EXACT_TARGET_OK lStepEmbeddingGeometry LStepEmbeddingGeometryTarget"
  let info ← getConstInfo `BfgsVerification.lStepEmbeddingPolyhedral
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LStepEmbeddingPolyhedralTarget)
  unless ok do throwError "target mismatch: lStepEmbeddingPolyhedral"
  logInfo "EXACT_TARGET_OK lStepEmbeddingPolyhedral LStepEmbeddingPolyhedralTarget"
  let info ← getConstInfo `BfgsVerification.lStepEmbeddingCopies
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LStepEmbeddingCopiesTarget)
  unless ok do throwError "target mismatch: lStepEmbeddingCopies"
  logInfo "EXACT_TARGET_OK lStepEmbeddingCopies LStepEmbeddingCopiesTarget"
