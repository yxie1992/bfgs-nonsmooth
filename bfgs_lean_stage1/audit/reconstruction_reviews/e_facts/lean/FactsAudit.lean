import EReconstructionFacts
noncomputable section
open BfgsVerification
open Lean Elab Command in
run_cmd do
  let names := #[``BfgsVerification.EReconstruction.eventually_below_tolerance,
    ``BfgsVerification.EReconstruction.planar_eventual_printed_tolerance,
    ``BfgsVerification.EReconstruction.spike_eventual_printed_tolerance,
    ``BfgsVerification.EReconstruction.inverse_update_secant,
    ``BfgsVerification.EReconstruction.hessian_update_secant,
    ``BfgsVerification.EReconstruction.ReconstructedFactsTarget,
    ``BfgsVerification.EReconstruction.reconstructedFacts]
  for name in names do
    let info ← getConstInfo name
    let signature ← liftTermElabM do pure (← Meta.ppExpr info.type).pretty
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"
    logInfo m!"E_FACT_AUDIT {Json.compress <| Json.mkObj [
      ("declaration",toJson name.toString),("signature",toJson signature),
      ("axioms",toJson (axioms.map Name.toString))]}"

/-- Independently written literal contract, with all four clauses and original
actual-run hypotheses visible. The source target alias is not its definition. -/
def ExpectedReconstructedFacts : Prop :=
  (∀ (n : ℕ) (H : Mat n) (s y : Vec n), dot y s ≠ 0 →
    (inverseBFGS H s y).mulVec y = s) ∧
  (∀ (n : ℕ) (H : Mat n), H.PosDef → ∀ (s y : Vec n), 0 < dot y s →
    ((inverseBFGS H s y)⁻¹).mulVec s = y) ∧
  (∀ (R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective),
    PlanarQuadraticExample.objective (R.x 0) < 1/100 →
    ∃ N, ∀ k ≥ N, PlanarQuadraticExample.objective (R.x k) < (10 : ℝ)^(-45 : ℤ)) ∧
  (∀ (n : ℕ) (a : Vec n), sqNorm a = 1 →
    ∀ (R : AdmissibleBFGSRun n (NormalSpike.objective a)),
    ∃ N, ∀ k ≥ N, NormalSpike.objective a (R.x k) < (10 : ℝ)^(-28 : ℤ))

open Lean Elab Command in
run_cmd do
  let ok ← liftTermElabM do
    Meta.isDefEq (← Meta.inferType (mkConst ``BfgsVerification.EReconstruction.reconstructedFacts))
      (mkConst ``ExpectedReconstructedFacts)
  unless ok do throwError "independent literal facts contract mismatch"
  let ok ← liftTermElabM do
    Meta.isDefEq (← Meta.inferType (mkConst ``BfgsVerification.EReconstruction.reconstructedFacts))
      (mkConst ``BfgsVerification.EReconstruction.ReconstructedFactsTarget)
  unless ok do throwError "public target mismatch"
  logInfo "E_FACT_TARGET_PASS 2"
