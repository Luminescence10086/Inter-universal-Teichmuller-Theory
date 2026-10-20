import Lean
import IUTBridge

/-! Infrastructure only. Export all project constants, including private/auxiliary
definitions, so the consumer can follow dependencies through helper constants.
The module filter is restricted to `IUTBridge`, so imported `LocalFieldAudit` and
Mathlib constants stay external metadata and never become fact-tree nodes. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if moduleName.toString == "IUTBridge" || moduleName.toString.startsWith "IUTBridge." then
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
