import Lean
import Boundary.ThetaGermTransport

open Lean Elab Command Meta

/-! Mechanical export for the 18 declarations selected by the current
`Boundary.ThetaGermTransport.lean` `#print axioms` list. The graph includes only the
transitive type/value-constant closure owned by that module. -/

private def thetaGermTransportRequestedNames : Array Name := #[
  ``CoreThetaGermTransport.summable_germ_coefficient,
  ``CoreThetaGermTransport.thetaTerm_q_shift,
  ``CoreThetaGermTransport.thetaGerm_q_mul,
  ``CoreThetaGermTransport.theta_q_mul_ne_zero,
  ``CoreThetaGermTransport.coordinateUnit,
  ``CoreThetaGermTransport.coe_coordinateUnit,
  ``CoreThetaGermTransport.constantUnit,
  ``CoreThetaGermTransport.coe_constantUnit,
  ``CoreThetaGermTransport.thetaGermUnit_q_mul,
  ``CoreThetaGermTransport.map_thetaGermUnit_q_mul,
  ``CoreThetaGermTransport.toFieldUnits,
  ``CoreThetaGermTransport.kummer_thetaGermUnit_q_mul,
  ``CoreThetaGermTransport.reducedGermHom,
  ``CoreThetaGermTransport.reduced_coordinate_eq_one,
  ``CoreThetaGermTransport.reduced_constant,
  ``CoreThetaGermTransport.reduced_thetaGermUnit_q_mul,
  ``CoreThetaGermTransport.exponent_theta_q_mul,
  ``CoreThetaGermTransport.principal_eq_iff_zero_automorphy_exponent
]

private def uniqueThetaGermTransportNames (names : Array Name) : Array Name :=
  names.foldl (fun acc name => if acc.contains name then acc else acc.push name) #[]

private def thetaGermTransportDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    dependencies := dependencies ++ value.getUsedConstants
  return uniqueThetaGermTransportNames dependencies

private def thetaGermTransportKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def thetaGermTransportModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "<no-module-index>"
  | some idx => env.header.moduleNames[idx]!.toString

private partial def collectThetaGermTransportClosure (env : Environment) (ownerModule : ModuleIdx)
    (todo : List Name) (seen : NameSet := {}) (ordered : Array Name := #[]) : Array Name :=
  match todo with
  | [] => ordered
  | name :: rest =>
    if seen.contains name then
      collectThetaGermTransportClosure env ownerModule rest seen ordered
    else
      let seen := seen.insert name
      if env.getModuleIdxFor? name != some ownerModule then
        collectThetaGermTransportClosure env ownerModule rest seen ordered
      else
        match env.find? name with
        | none => collectThetaGermTransportClosure env ownerModule rest seen ordered
        | some info =>
          let dependencies := thetaGermTransportDependencies info
          collectThetaGermTransportClosure env ownerModule (dependencies.toList ++ rest)
            seen (ordered.push name)

elab "#export_theta_germ_transport" : command => do
  let env ← getEnv
  let some ownerModule := env.getModuleIdxFor? ``CoreThetaGermTransport.summable_germ_coefficient
    | throwError "Boundary.ThetaGermTransport module index was not found"
  for name in thetaGermTransportRequestedNames do
    unless (env.find? name).isSome do
      throwError "selected declaration was not found: {name}"
  let localNames :=
    collectThetaGermTransportClosure env ownerModule thetaGermTransportRequestedNames.toList
  let json ← liftTermElabM do
    let mut nodes := #[]
    for name in localNames do
      let some info := (← getEnv).find? name
        | throwError "local declaration disappeared from environment: {name}"
      let statement ← ppExpr info.type
      let constants := (thetaGermTransportDependencies info).map fun dependency =>
        toJson dependency.toString
      nodes := nodes.push <| Json.mkObj [
        ("id", toJson name.toString),
        ("module", toJson (thetaGermTransportModuleName (← getEnv) name)),
        ("kind", toJson (thetaGermTransportKind info)),
        ("statement", toJson statement.pretty),
        ("constants", Json.arr constants)
      ]
    return Json.arr nodes
  IO.println json.compress

#export_theta_germ_transport
