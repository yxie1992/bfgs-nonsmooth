import BfgsVerification.LStableInvariantManifold
open Lean Elab Command in
run_cmd do
  for (decl,target) in [
    (`BfgsVerification.LReturnStableGraph.lStableManifold, `BfgsVerification.LReturnStableGraph.LStableManifoldTarget),
    (`BfgsVerification.LReturnStableGraph.lStableInvariantManifold, `BfgsVerification.LReturnStableGraph.LStableInvariantManifoldTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "stable manifold exact type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
