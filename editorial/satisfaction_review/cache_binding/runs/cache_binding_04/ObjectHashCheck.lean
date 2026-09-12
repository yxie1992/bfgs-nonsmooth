import Lake
open Lake System Lean

def main (args : List String) : IO UInt32 := do
  let [input] := args | throw <| IO.userError "expected one input list"
  let root := (← IO.currentDir).parent.getD "."
  let names := (← IO.FS.readFile input).splitOn "\n" |>.filter (· != "")
  let mut rows : Array Json := #[]
  let mut mismatches := 0
  for name in names do
    let path := root / name
    let actual ← computeBinFileHash path
    let hashFile := FilePath.mk (path.toString ++ ".hash")
    let present ← hashFile.pathExists
    let cached ← if present then Hash.load? hashFile else pure none
    if present && cached != some actual then
      mismatches := mismatches + 1
    rows := rows.push <| Json.mkObj [
      ("path", toJson name), ("actual_lake_binary_hash", toJson actual.toString),
      ("hash_sidecar_present", toJson present),
      ("recorded_lake_binary_hash", toJson (cached.map toString))]
  IO.println <| (Json.mkObj [("objects", Json.arr rows),
    ("mismatch_count", toJson mismatches)]).compress
  return if mismatches == 0 then 0 else 1
