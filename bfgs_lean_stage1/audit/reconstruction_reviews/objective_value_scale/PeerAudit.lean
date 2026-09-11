import ObjectiveValueScalingTargets
import Lean
#check BfgsVerification.ObjectiveValueScale.objective
#print axioms BfgsVerification.ObjectiveValueScale.objective
#check BfgsVerification.ObjectiveValueScale.convex
#print axioms BfgsVerification.ObjectiveValueScale.convex
#check BfgsVerification.ObjectiveValueScale.gradientFunctional_scale
#print axioms BfgsVerification.ObjectiveValueScale.gradientFunctional_scale
#check BfgsVerification.ObjectiveValueScale.hasGradient
#print axioms BfgsVerification.ObjectiveValueScale.hasGradient
#check BfgsVerification.ObjectiveValueScale.step
#print axioms BfgsVerification.ObjectiveValueScale.step
#check BfgsVerification.ObjectiveValueScale.update
#print axioms BfgsVerification.ObjectiveValueScale.update
#check BfgsVerification.ObjectiveValueScale.posDef
#print axioms BfgsVerification.ObjectiveValueScale.posDef
#check BfgsVerification.ObjectiveValueScale.energy
#print axioms BfgsVerification.ObjectiveValueScale.energy
#check BfgsVerification.ObjectiveValueScale.run
#print axioms BfgsVerification.ObjectiveValueScale.run
#check BfgsVerification.ObjectiveValueScale.run_x
#print axioms BfgsVerification.ObjectiveValueScale.run_x
#check BfgsVerification.ObjectiveValueScale.run_H
#print axioms BfgsVerification.ObjectiveValueScale.run_H
#check BfgsVerification.ObjectiveValueScale.run_g
#print axioms BfgsVerification.ObjectiveValueScale.run_g
#check BfgsVerification.ObjectiveValueScale.run_alpha
#print axioms BfgsVerification.ObjectiveValueScale.run_alpha
#check BfgsVerification.ObjectiveValueScale.run_c1
#print axioms BfgsVerification.ObjectiveValueScale.run_c1
#check BfgsVerification.ObjectiveValueScale.run_c2
#print axioms BfgsVerification.ObjectiveValueScale.run_c2
#check BfgsVerification.ObjectiveValueScale.run_value
#print axioms BfgsVerification.ObjectiveValueScale.run_value
#check BfgsVerification.ObjectiveValueScale.run_q
#print axioms BfgsVerification.ObjectiveValueScale.run_q
#check BfgsVerification.ObjectiveValueScale.run_d
#print axioms BfgsVerification.ObjectiveValueScale.run_d
#check BfgsVerification.ObjectiveValueScale.run_displacement
#print axioms BfgsVerification.ObjectiveValueScale.run_displacement
#check BfgsVerification.ObjectiveValueScale.run_gradientChange
#print axioms BfgsVerification.ObjectiveValueScale.run_gradientChange
#check BfgsVerification.ObjectiveValueScale.run_curvature
#print axioms BfgsVerification.ObjectiveValueScale.run_curvature
#check BfgsVerification.ObjectiveValueScale.optimizerIntercept
#print axioms BfgsVerification.ObjectiveValueScale.optimizerIntercept
#check BfgsVerification.ObjectiveValueScale.secantCurvature
#print axioms BfgsVerification.ObjectiveValueScale.secantCurvature
#check BfgsVerification.ObjectiveValueScalingTarget
#print axioms BfgsVerification.ObjectiveValueScalingTarget
#check BfgsVerification.objectiveValueScaling
#print axioms BfgsVerification.objectiveValueScaling

open BfgsVerification
private def IndependentlyRestated : Prop :=
  ∀ n (F : Vec n → ℝ) (a b : ℝ), 0 < a →
    ∀ R : AdmissibleBFGSRun n F,
      ∃ S : AdmissibleBFGSRun n (fun x => a * F x + b),
        S.c₁ = R.c₁ ∧ S.c₂ = R.c₂ ∧
        ∀ k : ℕ, S.x k = R.x k ∧ S.H k = a⁻¹ • R.H k ∧
          S.g k = a • R.g k ∧ S.α k = R.α k ∧
          S.d k = a * R.d k ∧ S.curvature k = a * R.curvature k
open Lean Elab Command in
run_cmd do
  let i ← getConstInfo `BfgsVerification.objectiveValueScaling
  let a ← liftTermElabM <| Meta.isDefEq i.type (mkConst ``IndependentlyRestated)
  let b ← liftTermElabM <| Meta.isDefEq (mkConst `BfgsVerification.ObjectiveValueScalingTarget) (mkConst ``IndependentlyRestated)
  unless a && b do throwError "Full source contract mismatch"
  logInfo "PEER_FULL_CONTRACT_OK wrapper"
  logInfo "PEER_FULL_CONTRACT_OK target"
