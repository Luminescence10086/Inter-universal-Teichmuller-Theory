import IUTBridge

/-! Infrastructure only. Report the actual import closure so the verifier can
hash the compiled artifacts it depends on. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, m) in env.header.moduleNames.mapIdx fun i m => (i, m) do
    let _ := n
    rows := rows.push <| Json.mkObj [("module", toJson m.toString)]
  logInfo (Json.compress (toJson rows))
