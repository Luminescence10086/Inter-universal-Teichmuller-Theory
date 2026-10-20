import Lean
import IUTBridge

/-! Diagnostic export, not a theorem. Definition bodies augment the statement
change ledger; no cross-version semantic equivalence is asserted. -/
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option maxRecDepth 100000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if moduleName.toString == "IUTBridge" || moduleName.toString.startsWith "IUTBridge." then
      if let .defnInfo info := ci then
        let body ← liftTermElabM <| Meta.ppExpr info.value
        rows := rows.push <| Json.mkObj [("id", toJson n.toString),
          ("body", toJson body.pretty)]
  logInfo (Json.compress (toJson rows))
