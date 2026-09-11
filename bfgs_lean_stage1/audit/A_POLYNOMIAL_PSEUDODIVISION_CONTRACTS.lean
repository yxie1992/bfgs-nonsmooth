import BfgsVerification.PseudoDivisionTargets
open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.positivePseudoDivision, `BfgsVerification.PositivePseudoDivisionTarget),
    (`BfgsVerification.pseudoDivisionSpecialization, `BfgsVerification.PseudoDivisionSpecializationTarget),
    (`BfgsVerification.finiteRootRemainders, `BfgsVerification.FiniteRootRemaindersTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
