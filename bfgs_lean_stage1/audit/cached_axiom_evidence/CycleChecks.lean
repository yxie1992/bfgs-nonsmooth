import CachedAxiomGraph

open ExperimentalAxiomAudit Lean Elab Command in
run_cmd do
  -- Edges are dependency -> its users. A reached node depends on the seed.
  let cases : Array (String × Array (Array Nat) × Nat × Array Bool) := #[
    ("isolated", #[#[]], 0, #[true]),
    ("self-cycle", #[#[0]], 0, #[true]),
    ("mutual-cycle", #[#[1],#[0]], 0, #[true,true]),
    ("cycle-with-exit-to-axiom", #[#[1],#[2],#[1]], 0, #[true,true,true]),
    ("unreachable-cycle", #[#[],#[2],#[1]], 0, #[true,false,false]),
    ("diamond-and-cycle", #[#[1,2],#[3],#[3],#[4],#[3]],0,#[true,true,true,true,true])]
  for (label, edges, seed, expected) in cases do
    unless reverseReach edges seed == expected do throwError "cycle mismatch: {label}"
    logInfo m!"GRAPH_CASE_OK {label}"
  -- Two independent axiom seeds: a cycle inherits both, but isolated axiom C
  -- must not leak into any other constant's result.
  let names := #[`A,`B,`C,`p,`q,`none]
  let graph : GraphState := {
    names := names
    indices := names.foldl (fun state name => state.insert name state.size) {}
    dependencies := #[#[],#[],#[],#[`q,`A],#[`p,`B],#[`none]]
    axiomIndices := #[0,1,2] }
  let expected := #[#[`A],#[`B],#[`C],#[`A,`B],#[`A,`B],#[]]
  unless allAxiomSets graph == expected do throwError "shared-cycle axiom-union mismatch"
  logInfo "GRAPH_CASE_OK multiple-axioms-and-unreachable-cycle"
