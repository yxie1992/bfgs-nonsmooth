import Lake
open Lake System

def main : IO Unit := do
  let widget : FilePath := ".lake/packages/proofwidgets/widget"
  for name in ["package-lock.json", "package.json"] do
    let path := widget / name
    IO.println s!"{path}: text={← computeTextFileHash path}; binary={← computeBinFileHash path}"
  let entries ← (widget / "src").readDir
  let sources := entries.filterMap fun entry =>
    match entry.path.extension with
    | some "ts" | some "tsx" | some "js" | some "jsx" => some entry.path
    | _ => none
  let sources := sources.qsort (toString · < toString ·)
  let mut h := Hash.nil
  for path in sources ++ #[widget / "rollup.config.js", widget / "tsconfig.json"] do
    h := h.mix (← computeTextFileHash path)
  let actual := h.mix (← computeTextFileHash (widget / "package-lock.json"))
  let cached ← Hash.load? (widget / "package-lock.json.hash")
  IO.println s!"JS target dependency hash with actual package-lock bytes: {actual}"
  IO.println s!"JS target dependency hash with cached package-lock hash: {cached.map h.mix}"
