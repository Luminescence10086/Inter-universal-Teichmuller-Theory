import Lean
import IUTAudit

/-! Infrastructure only: extract actual elaborated theorem terms and their axioms. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "IUTAudit." then
      if let .thmInfo info := ci then
        let used := (info.type.getUsedConstants ++ info.value.getUsedConstants).toList.eraseDups
        let axioms ← collectAxioms n
        let type ← liftTermElabM <| Meta.ppExpr info.type
        rows := rows.push <| Json.mkObj [
          ("id", toJson n.toString),
          ("statement", toJson type.pretty),
          ("constants", toJson (used.map Name.toString)),
          ("axioms", toJson (axioms.map Name.toString))]
  logInfo (Json.compress (toJson rows))
-- temporary hash freshness probe only
