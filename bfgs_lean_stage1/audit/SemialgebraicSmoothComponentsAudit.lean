import BfgsVerification.SemialgebraicSmoothComponents

#check BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components
#print axioms BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components
#check BfgsVerification.SemialgebraicSmoothComponentsTarget
#print axioms BfgsVerification.SemialgebraicSmoothComponentsTarget
#check BfgsVerification.semialgebraicSmoothComponents
#print axioms BfgsVerification.semialgebraicSmoothComponents

open Lean Elab Command in
run_cmd do
  for d in [`BfgsVerification.RealAlgebraicGeometry.semialgebraic_smooth_components,
      `BfgsVerification.semialgebraicSmoothComponents] do
    let ok ← liftTermElabM do
      let e ← Meta.mkConstWithFreshMVarLevels d
      let ty ← Meta.inferType e
      Meta.isDefEq ty (mkConst `BfgsVerification.SemialgebraicSmoothComponentsTarget)
    unless ok do throwError "actual smooth-component exact contract mismatch: {d}"
    logInfo m!"EXACT_TARGET_OK {d}"
