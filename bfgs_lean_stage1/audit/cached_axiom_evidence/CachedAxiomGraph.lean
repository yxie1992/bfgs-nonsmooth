import Lean

namespace ExperimentalAxiomAudit
open Lean

-- Match Lean.Util.CollectAxioms.collect case by case. In particular do not use
-- ConstantInfo.getUsedConstantsAsSet, whose recursion/axiom cases differ.
def directDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo _ => #[]
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

structure GraphState where
  indices : Std.HashMap Name Nat := {}
  names : Array Name := #[]
  dependencies : Array (Array Name) := #[]
  axiomIndices : Array Nat := #[]
  missing : Array Name := #[]

-- This phase caches only complete outgoing edges, never incomplete axiom sets.
partial def visit (env : Environment) (name : Name) : StateM GraphState Unit := do
  unless (← get).indices.contains name do
    let index := (← get).names.size
    let info := env.checked.get.find? name
    let deps := info.map directDependencies |>.getD #[]
    modify fun state => { state with
      indices := state.indices.insert name index
      names := state.names.push name
      dependencies := state.dependencies.push deps
      axiomIndices := match info with
        | some (.axiomInfo _) => state.axiomIndices.push index
        | _ => state.axiomIndices
      missing := if info.isNone then state.missing.push name else state.missing }
    deps.forM (visit env)

-- A worklist search on reversed edges reaches exactly the constants that can
-- reach its axiom seed. Visited indices make self/mutual cycles harmless.
def reverseReach (reverseEdges : Array (Array Nat)) (seed : Nat) : Array Bool := Id.run do
  let mut seen := (Array.replicate reverseEdges.size false).set! seed true
  let mut pending := #[seed]
  while !pending.isEmpty do
    let index := pending.back!
    pending := pending.pop
    for parent in reverseEdges[index]! do
      if !seen[parent]! then
        seen := seen.set! parent true
        pending := pending.push parent
  return seen

def allAxiomSets (graph : GraphState) : Array (Array Name) := Id.run do
  let mut reverseEdges : Array (Array Nat) := Array.replicate graph.names.size #[]
  for index in [:graph.names.size] do
    for dependency in graph.dependencies[index]! do
      let child := graph.indices[dependency]!
      reverseEdges := reverseEdges.modify child (fun edges => edges.push index)
  let mut results : Array (Array Name) := Array.replicate graph.names.size #[]
  for seed in graph.axiomIndices do
    let reached := reverseReach reverseEdges seed
    for index in [:graph.names.size] do
      if reached[index]! then
        results := results.modify index (fun deps => deps.push graph.names[seed]!)
  return results

end ExperimentalAxiomAudit
