import BfgsVerification
import Lean

namespace BfgsAuditCache
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

end BfgsAuditCache


namespace Master21Audit
open Lean

def moduleFor (env : Environment) (name : Name) : Name :=
  ((env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i.toNat]!)).getD .anonymous

def ownedModule (name : Name) : Bool :=
  (`BfgsVerification).isPrefixOf name

def owned (env : Environment) (name : Name) : Bool := ownedModule (moduleFor env name)

def kind (info : ConstantInfo) : String := match info with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .inductInfo _ => "inductive"

def projectDependencies (env : Environment) (e : Expr) : Array String :=
  ((e.getUsedConstants.filter (owned env)).qsort Name.lt).map Name.toString

end Master21Audit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Lean Elab Command BfgsAuditCache Master21Audit in
run_cmd do
  let started ← IO.monoMsNow
  let env ← getEnv
  let mut all := #[]
  let mut roots := #[]
  for (name, info) in env.constants.toList do
    if owned env name then
      all := all.push name
      if !info.isUnsafe && !info.isPartial then
        roots := roots.push name
  all := all.qsort Name.lt
  roots := roots.qsort Name.lt
  let (_, graph) := (roots.forM (visit env)).run {}
  unless graph.missing.isEmpty do
    throwError "unresolved checked constants: {graph.missing}"
  let mut badReachability := #[]
  for name in graph.names do
    let some ci := env.checked.get.find? name | throwError "missing graph constant {name}"
    if ci.isUnsafe || ci.isPartial then badReachability := badReachability.push name
  unless badReachability.isEmpty do
    throwError "safe mathematical root reaches unsafe/partial implementation: {badReachability}"
  let sets := allAxiomSets graph
  let mut reports := #[]
  let mut excluded := #[]
  for name in all do
    let info ← getConstInfo name
    let some checked := env.checked.get.find? name | throwError "unchecked project constant {name}"
    unless info.type == checked.type do throwError "checked/elaboration type mismatch {name}"
    unless directDependencies info == directDependencies checked do
      throwError "checked/elaboration dependency mismatch {name}"
    unless kind info == kind checked && info.isUnsafe == checked.isUnsafe &&
        info.isPartial == checked.isPartial && info.levelParams == checked.levelParams do
      throwError "checked/elaboration metadata mismatch {name}"
    let info := checked
    let signature ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    let isProp : Option Bool ← if info.isUnsafe || info.isPartial then pure none
      else liftTermElabM do return some (← Meta.isProp info.type)
    let ranges ← findDeclarationRangesCore? name
    let sourceRange := ranges.map fun r => Json.mkObj [
      ("start_line", toJson r.range.pos.line), ("start_column", toJson r.range.pos.column),
      ("end_line", toJson r.range.endPos.line), ("end_column", toJson r.range.endPos.column)]
    let typeDeps := projectDependencies env info.type
    let valueDeps := (info.value? (allowOpaque := true)).map (projectDependencies env) |>.getD #[]
    let structureDeps := match info with
      | .inductInfo v => v.ctors.toArray.filter (owned env) |>.map Name.toString
      | _ => #[]
    let fields := [
      ("name",toJson name.toString), ("module",toJson (moduleFor env name).toString),
      ("kind",toJson (kind info)), ("unsafe",toJson info.isUnsafe), ("partial",toJson info.isPartial),
      ("isProp",toJson isProp), ("signature",toJson signature),
      ("level_params",toJson (info.levelParams.map Name.toString)),
      ("source_range",sourceRange.getD Json.null),
      ("has_private_prefix",toJson (name.toString.startsWith "_private.")),
      ("type_project_dependencies",toJson typeDeps), ("value_project_dependencies",toJson valueDeps),
      ("structural_project_dependencies",toJson structureDeps),
      ("in_legacy_namespace",toJson ((`BfgsVerification).isPrefixOf name))]
    if info.isUnsafe || info.isPartial then
      excluded := excluded.push <| Json.mkObj fields
    else
      let axioms := sets[graph.indices[name]!]! |>.qsort Name.lt
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "unexpected mathematical axiom {ax} in {name}"
      reports := reports.push <| Json.mkObj (fields ++ [("axioms",toJson (axioms.map Name.toString))])
  let out := (← IO.getEnv "BFGS_MASTER21_AUDIT_OUT").getD "audit/scratch/master21/audit_dl_e/"
  IO.FS.writeFile (out ++ "all_safe_declarations.json") (Json.arr reports |>.compress)
  IO.FS.writeFile (out ++ "compiler_implementation_declarations.json") (Json.arr excluded |>.compress)
  let stats := Json.mkObj [
    ("module_names",toJson (env.header.moduleNames.filter ownedModule |>.map Name.toString)),
    ("all_owned_constants",toJson all.size), ("safe_roots",toJson roots.size),
    ("excluded_compiler_constants",toJson excluded.size),
    ("missing",toJson (graph.missing.map Name.toString)),
    ("unsafe_or_partial_reachable",toJson (badReachability.map Name.toString)),
    ("axiom_seeds",toJson (graph.axiomIndices.map (fun i => graph.names[i]!.toString))),
    ("graph_vertices",toJson graph.names.size),
    ("elapsed_ms",toJson ((← IO.monoMsNow)-started))]
  IO.FS.writeFile (out ++ "all_declaration_stats.json") stats.pretty
  logInfo m!"MASTER21_ALL_DECLARATIONS_PASS {stats.compress}"
