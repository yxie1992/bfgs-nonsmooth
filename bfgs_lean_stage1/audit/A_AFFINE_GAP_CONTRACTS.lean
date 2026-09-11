import BfgsVerification.AffineGapTargets
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.finiteC1MaxAffineGap
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.FiniteC1MaxAffineGapTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK finiteC1MaxAffineGap FiniteC1MaxAffineGapTarget"
