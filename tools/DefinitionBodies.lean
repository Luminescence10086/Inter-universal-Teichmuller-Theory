import Lean
import IUTAudit

/-! Diagnostic export, not a theorem. Full pretty-printed definition bodies are
used as conservative change fingerprints. Text equality is not proof transfer. -/
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
    if moduleName.toString == "IUTAudit" || moduleName.toString.startsWith "IUTAudit." then
      if let .defnInfo info := ci then
        let body ← liftTermElabM <| Meta.ppExpr info.value
        rows := rows.push <| Json.mkObj [("id", toJson n.toString),
          ("body", toJson body.pretty)]
  logInfo (Json.compress (toJson rows))
