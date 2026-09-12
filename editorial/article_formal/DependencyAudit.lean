import ArticleGeometry
import ConvexBalance
import Lean
import Lean.Util.CollectAxioms

/-! Independent metadata audit, never an input to a mathematical proof. -/
namespace ArticleFormalAudit
open Lean

def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo _ => #[]
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

def moduleOf (env : Environment) (name : Name) : Name :=
  ((env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i.toNat]!)).getD .anonymous

def owned (env : Environment) (name : Name) : Bool :=
  let module := moduleOf env name
  module == `ArticleGeometry || module == `ConvexBalance

def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .inductInfo _ => "inductive"

end ArticleFormalAudit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Lean Elab Command ArticleFormalAudit in
run_cmd do
  let env ← getEnv
  let mut roots := #[]
  for (name, _) in env.constants.toList do
    if owned env name then roots := roots.push name
  roots := roots.qsort Name.lt
  unless !roots.isEmpty do throwError "No article module-owned declarations found"
  let mut seen : Std.HashSet Name := {}
  let mut pending := roots
  let mut graph : Array Json := #[]
  let mut axiomNames : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.checked.get.find? name
        | throwError "Unchecked or missing dependency: {name}"
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial reachable declaration: {name}"
      let deps := dependencies info |>.qsort Name.lt
      pending := pending ++ deps
      if kind info == "axiom" then
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Unapproved axiom: {name}"
        axiomNames := axiomNames.push name
      graph := graph.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson (moduleOf env name).toString),
        ("kind", toJson (kind info)), ("unsafe", toJson info.isUnsafe),
        ("partial", toJson info.isPartial),
        ("dependencies", toJson (deps.map Name.toString))]
  let mut reports : Array Json := #[]
  for name in roots do
    let info ← getConstInfo name
    let some checked := env.checked.get.find? name | throwError "Unchecked root: {name}"
    unless info.type == checked.type && dependencies info == dependencies checked do
      throwError "Elaborator/kernel root mismatch: {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Ordinary collector found unexpected axiom {ax} in {name}"
    let signature ← liftTermElabM do return (← Meta.ppExpr checked.type).pretty
    let ranges ← findDeclarationRangesCore? name
    let range := ranges.map fun r => Json.mkObj [
      ("start_line",toJson r.range.pos.line), ("end_line",toJson r.range.endPos.line)]
    reports := reports.push <| Json.mkObj [
      ("name",toJson name.toString), ("module",toJson (moduleOf env name).toString),
      ("kind",toJson (kind checked)), ("signature",toJson signature),
      ("source_range",range.getD Json.null),
      ("unsafe",toJson checked.isUnsafe), ("partial",toJson checked.isPartial),
      ("private",toJson (name.toString.startsWith "_private.")),
      ("dependencies",toJson (dependencies checked |>.qsort Name.lt |>.map Name.toString)),
      ("axioms",toJson (axs.qsort Name.lt |>.map Name.toString))]
  let some output ← IO.getEnv "BFGS_ARTICLE_AUDIT_OUT"
    | throwError "Set BFGS_ARTICLE_AUDIT_OUT to an existing repository directory"
  IO.FS.writeFile (output ++ "/declarations.json") (Json.arr reports |>.pretty)
  IO.FS.writeFile (output ++ "/dependency_graph.json") (Json.arr graph |>.compress)
  let summary := Json.mkObj [
    ("status",toJson "PASS"), ("module_owned_declarations",toJson roots.size),
    ("transitive_checked_declarations",toJson seen.size),
    ("axioms",toJson (axiomNames.qsort Name.lt |>.map Name.toString)),
    ("unchecked_missing_unsafe_partial",toJson (#[] : Array String)),
    ("collector",toJson "Lean.collectAxioms plus independent full checked dependency traversal")]
  IO.FS.writeFile (output ++ "/audit_summary.json") summary.pretty
  logInfo m!"ARTICLE_GEOMETRY_AUDIT {summary.compress}"
