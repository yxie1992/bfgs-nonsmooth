import ReconstructedFourPieceTargets
import Lean

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
open BfgsVerification BfgsVerification.ReconstructedFourPiece
  BfgsVerification.RadialCertificate

private def IndependentlyRestatedFailure : Prop :=
  ConvexOn ℝ univ objective ∧
    (∀ b : ℝ, IsCompact {z | objective z ≤ b}) ∧
    optimizer = (![-1, 5] : Vec 2) ∧ objective optimizer = -1 ∧
    (∀ z, -1 ≤ objective z) ∧ (∀ z, objective z = -1 → z = optimizer) ∧
    (∀ i : Fin 3, family.branch i.castSucc optimizer = (![-1, -1, -29 / 4] : Vec 3) i) ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective 0 ∧
    ∀ c₁ c₂ : ℝ, ∀ h₁ : 0 < c₁, ∀ h₁' : c₁ ≤ 1 / 3,
      ∀ h₁₂ : c₁ < c₂, ∀ h₂ : c₂ < 1,
      let R : AdmissibleBFGSRun 2 objective := run h₁ h₁' h₁₂ h₂
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
      (∀ k, R.x k = AffineWhitening.point coordinate (SeedOrbit.orbitPoint k)) ∧
      (∀ k, R.H k = valueScale⁻¹ • AffineWhitening.metric coordinate (SeedOrbit.orbitMetric k)) ∧
      (∀ k, R.g k = valueScale • AffineWhitening.gradient coordinate (SeedOrbit.orbitGradient k)) ∧
      (∀ k, R.α k = SeedOrbit.orbitLength k) ∧
      Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 (valueScale - 1)) ∧
      -1 < valueScale - 1 ∧
      (∀ k, valueScale - 1 < objective (R.x k)) ∧
      (∀ k, objective (R.x (k + 1)) < objective (R.x k))

private def IndependentlyRestatedPredictions : Prop :=
  (∀ m : ℕ, ∀ j : Fin 3,
    optimizerIntercept objective optimizer (point (3 * m + j.val)) (gradient (3 * m + j.val)) =
      (![0, 0, 25 / 4] : Vec 3) j) ∧
    (∀ k, HasFDerivAt objective (gradientFunctional (gradient k)) (point k)) ∧
    (∀ k, 0 < secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1))) ∧
    Tendsto (fun k => secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1)))
      atTop (𝓝 0) ∧
    ¬ HasInterceptBounds objective {z | objective z ≤ objective (point 0)} optimizer ∧
    ¬ HasRadialSecantBounds objective {z | objective z ≤ objective (point 0)} optimizer

open Lean Elab Command in
run_cmd do
  for (n, t, p) in [(`BfgsVerification.reconstructedFourPieceFailure,
      `BfgsVerification.ReconstructedFourPieceFailureTarget, ``IndependentlyRestatedFailure),
      (`BfgsVerification.reconstructedSupportingPlane,
       `BfgsVerification.ReconstructedSupportingPlaneTarget, ``IndependentlyRestatedPredictions)] do
    let info ← getConstInfo n
    let a ← liftTermElabM <| Meta.isDefEq info.type (mkConst p)
    let b ← liftTermElabM <| Meta.isDefEq (mkConst t) (mkConst p)
    unless a && b do throwError "Independent whole-contract mismatch: {n}"
    logInfo m!"PEER_COMPLETE_CONTRACT_OK {n}"
    logInfo m!"PEER_COMPLETE_CONTRACT_OK {t}"
