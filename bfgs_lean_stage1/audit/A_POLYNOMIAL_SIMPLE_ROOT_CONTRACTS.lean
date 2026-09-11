import BfgsVerification.PolynomialRootTargets
open Lean Elab Command in
run_cmd do
  for (decl, target) in [
    (`BfgsVerification.polynomialFiberDerivative, `BfgsVerification.PolynomialFiberDerivativeTarget),
    (`BfgsVerification.polynomialSimpleRootChart, `BfgsVerification.PolynomialSimpleRootChartTarget),
    (`BfgsVerification.polynomialSimpleRootProjection, `BfgsVerification.PolynomialSimpleRootProjectionTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "type mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
