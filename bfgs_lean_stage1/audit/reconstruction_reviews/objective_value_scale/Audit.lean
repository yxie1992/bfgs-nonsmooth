import ObjectiveValueScalingTargets
set_option pp.universes true
set_option pp.fullNames true
set_option maxHeartbeats 0

#check @BfgsVerification.ObjectiveValueScale.objective
#print axioms BfgsVerification.ObjectiveValueScale.objective
#check @BfgsVerification.ObjectiveValueScale.convex
#print axioms BfgsVerification.ObjectiveValueScale.convex
#check @BfgsVerification.ObjectiveValueScale.gradientFunctional_scale
#print axioms BfgsVerification.ObjectiveValueScale.gradientFunctional_scale
#check @BfgsVerification.ObjectiveValueScale.hasGradient
#print axioms BfgsVerification.ObjectiveValueScale.hasGradient
#check @BfgsVerification.ObjectiveValueScale.step
#print axioms BfgsVerification.ObjectiveValueScale.step
#check @BfgsVerification.ObjectiveValueScale.update
#print axioms BfgsVerification.ObjectiveValueScale.update
#check @BfgsVerification.ObjectiveValueScale.posDef
#print axioms BfgsVerification.ObjectiveValueScale.posDef
#check @BfgsVerification.ObjectiveValueScale.energy
#print axioms BfgsVerification.ObjectiveValueScale.energy
#check @BfgsVerification.ObjectiveValueScale.run
#print axioms BfgsVerification.ObjectiveValueScale.run
#check @BfgsVerification.ObjectiveValueScale.run_x
#print axioms BfgsVerification.ObjectiveValueScale.run_x
#check @BfgsVerification.ObjectiveValueScale.run_H
#print axioms BfgsVerification.ObjectiveValueScale.run_H
#check @BfgsVerification.ObjectiveValueScale.run_g
#print axioms BfgsVerification.ObjectiveValueScale.run_g
#check @BfgsVerification.ObjectiveValueScale.run_alpha
#print axioms BfgsVerification.ObjectiveValueScale.run_alpha
#check @BfgsVerification.ObjectiveValueScale.run_c1
#print axioms BfgsVerification.ObjectiveValueScale.run_c1
#check @BfgsVerification.ObjectiveValueScale.run_c2
#print axioms BfgsVerification.ObjectiveValueScale.run_c2
#check @BfgsVerification.ObjectiveValueScale.run_value
#print axioms BfgsVerification.ObjectiveValueScale.run_value
#check @BfgsVerification.ObjectiveValueScale.run_q
#print axioms BfgsVerification.ObjectiveValueScale.run_q
#check @BfgsVerification.ObjectiveValueScale.run_d
#print axioms BfgsVerification.ObjectiveValueScale.run_d
#check @BfgsVerification.ObjectiveValueScale.run_displacement
#print axioms BfgsVerification.ObjectiveValueScale.run_displacement
#check @BfgsVerification.ObjectiveValueScale.run_gradientChange
#print axioms BfgsVerification.ObjectiveValueScale.run_gradientChange
#check @BfgsVerification.ObjectiveValueScale.run_curvature
#print axioms BfgsVerification.ObjectiveValueScale.run_curvature
#check @BfgsVerification.ObjectiveValueScale.optimizerIntercept
#print axioms BfgsVerification.ObjectiveValueScale.optimizerIntercept
#check @BfgsVerification.ObjectiveValueScale.secantCurvature
#print axioms BfgsVerification.ObjectiveValueScale.secantCurvature
#check @BfgsVerification.ObjectiveValueScalingTarget
#print axioms BfgsVerification.ObjectiveValueScalingTarget
#check @BfgsVerification.objectiveValueScaling
#print axioms BfgsVerification.objectiveValueScaling

#print BfgsVerification.ObjectiveValueScalingTarget
example : BfgsVerification.ObjectiveValueScalingTarget := BfgsVerification.objectiveValueScaling
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.objectiveValueScaling
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.ObjectiveValueScalingTarget)
  unless ok do throwError "Exact target type mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.objectiveValueScaling"
