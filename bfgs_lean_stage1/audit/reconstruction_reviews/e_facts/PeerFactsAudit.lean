import EReconstructionFacts
noncomputable section
open BfgsVerification
open Lean Elab Command in
run_cmd do
  for name in #[``BfgsVerification.EReconstruction.eventually_below_tolerance,
      ``BfgsVerification.EReconstruction.planar_eventual_printed_tolerance,
      ``BfgsVerification.EReconstruction.spike_eventual_printed_tolerance,
      ``BfgsVerification.EReconstruction.inverse_update_secant,
      ``BfgsVerification.EReconstruction.hessian_update_secant,
      ``BfgsVerification.EReconstruction.ReconstructedFactsTarget,
      ``BfgsVerification.EReconstruction.reconstructedFacts] do
    let info ← getConstInfo name
    let ax ← Lean.collectAxioms name
    for a in ax do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected axiom {a}"
    let ty ← liftTermElabM do pure (← Meta.ppExpr info.type).pretty
    logInfo m!"E_FACT_PEER {Json.compress <| Json.mkObj [("declaration",toJson name.toString),("signature",toJson ty),("axioms",toJson (ax.map Name.toString))]}"

def PeerExpectedFacts : Prop :=
  (∀ (d : ℕ) (H : Mat d) (s y : Vec d), dot y s ≠ 0 →
    (inverseBFGS H s y).mulVec y = s) ∧
  (∀ (d : ℕ) (H : Mat d), H.PosDef → ∀ (s y : Vec d), 0 < dot y s →
    ((inverseBFGS H s y)⁻¹).mulVec s = y) ∧
  (∀ (run : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective),
    PlanarQuadraticExample.objective (run.x 0) < 1/100 →
    ∃ N : ℕ, ∀ k ≥ N, PlanarQuadraticExample.objective (run.x k) < (10 : ℝ)^(-45 : ℤ)) ∧
  (∀ (d : ℕ) (a : Vec d), sqNorm a = 1 →
    ∀ (run : AdmissibleBFGSRun d (NormalSpike.objective a)),
    ∃ N : ℕ, ∀ k ≥ N, NormalSpike.objective a (run.x k) < (10 : ℝ)^(-28 : ℤ))

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo ``BfgsVerification.EReconstruction.reconstructedFacts
  let ok ← liftTermElabM do Meta.isDefEq info.type (mkConst ``PeerExpectedFacts)
  unless ok do throwError "full source contract mismatch"
  let ok ← liftTermElabM do Meta.isDefEq (mkConst ``BfgsVerification.EReconstruction.ReconstructedFactsTarget) (mkConst ``PeerExpectedFacts)
  unless ok do throwError "target definition mismatch"
  logInfo "E_FACT_PEER_CONTRACT_PASS 2"
