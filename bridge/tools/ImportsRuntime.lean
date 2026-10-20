import Lean
import IUTBridge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for n in env.header.moduleNames do
    let path ← findOLean n
    rows := rows.push <| Json.mkObj [("module", toJson n.toString),
      ("path", toJson path.toString)]
  logInfo (Json.compress (toJson rows))
