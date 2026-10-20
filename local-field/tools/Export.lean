import Lean
import LocalFieldAudit

/-! Infrastructure only. Export all project constants, including private/auxiliary
definitions, so the consumer can follow dependencies through helper constants. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if moduleName.toString == "LocalFieldAudit" || moduleName.toString.startsWith "LocalFieldAudit." then
      let valueConsts := ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      let used := (ci.type.getUsedConstants ++ valueConsts).toList.eraseDups
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      let axioms ← collectAxioms n
      let type ← liftTermElabM <| Meta.ppExpr ci.type
      rows := rows.push <| Json.mkObj [
        ("id", toJson n.toString), ("module", toJson moduleName.toString),
        ("kind", toJson kind), ("statement", toJson type.pretty),
        ("constants", toJson (used.map Name.toString)),
        ("axioms", toJson (axioms.map Name.toString))]
  logInfo (Json.compress (toJson rows))
