import BfgsVerification
import CachedAxiomGraph
import CurrentRequestedNames

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Lean Elab Command ExperimentalAxiomAudit in
run_cmd do
  let started ← IO.monoMsNow
  let env ← getEnv
  let mut roots := #[]
  let mut seen : NameSet := {}
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if (`BfgsVerification).isPrefixOf name && info.isTheorem then
      roots := roots.push name
      seen := seen.insert name
      theoremCount := theoremCount + 1
  for name in currentRequestedNames do
    unless seen.contains name do
      roots := roots.push name
      seen := seen.insert name
  let (_, graph) := (roots.forM (visit env)).run {}
  unless graph.missing.isEmpty do
    throwError "missing checked constants: {graph.missing}"
  let graphFinished ← IO.monoMsNow
  logInfo m!"GRAPH_FINISHED {graph.names.size} vertices in {graphFinished-started}ms"
  let sets := allAxiomSets graph
  let setsFinished ← IO.monoMsNow
  logInfo m!"REACHABILITY_FINISHED {graph.axiomIndices.size} axiom seeds in {setsFinished-graphFinished}ms"
  let mut reports := #[]
  for name in roots do
    let info ← getConstInfo name
    let some checkedInfo := env.checked.get.find? name
      | throwError "requested root absent from checked environment: {name}"
    unless info.type == checkedInfo.type do
      throwError "checked/elaboration type mismatch: {name}"
    let signature ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let axiomNames := sets[graph.indices[name]!]! |>.qsort Name.lt
    reports := reports.push <| Json.mkObj [
      ("theorem", toJson name.toString),
      ("isTheorem", toJson info.isTheorem),
      ("axioms", toJson (axiomNames.map Name.toString)),
      ("signature", toJson signature)]
  let finished ← IO.monoMsNow
  let output := "audit/cached_axiom_evidence/"
  IO.FS.writeFile (output ++ "current_cached_reports.json") (Json.arr reports |>.compress)
  let edgeCount := graph.dependencies.foldl (fun n children => n+children.size) 0
  let stats := Json.mkObj [
    ("roots",toJson roots.size), ("actualTheorems",toJson theoremCount),
    ("graphVertices",toJson graph.names.size), ("graphEdges",toJson edgeCount),
    ("axiomSeeds",toJson (graph.axiomIndices.map (fun i => graph.names[i]!.toString))),
    ("missing",toJson (graph.missing.map Name.toString)),
    ("graphMs",toJson (graphFinished-started)),
    ("reachabilityMs",toJson (setsFinished-graphFinished)),
    ("typesMs",toJson (finished-setsFinished)), ("totalMs",toJson (finished-started))]
  IO.FS.writeFile (output ++ "current_cached_stats.json") stats.pretty
  logInfo m!"CACHED_AUDIT_FINISHED {stats.compress}"
