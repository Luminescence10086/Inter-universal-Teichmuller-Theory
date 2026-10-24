import Lean
import Boundary.AnchoredComparison

open Lean Elab Command Meta

/-! Mechanical export for the 15 declarations selected by the current
`Boundary.AnchoredComparison.lean` `#print axioms` list. The graph includes only the
transitive type/value-constant closure owned by that module. -/

private def anchoredRequestedNames : Array Name := #[
  ``CoreAnchoredComparison.dvd_determinant,
  ``CoreAnchoredComparison.cancel_anchor_precision,
  ``CoreAnchoredComparison.coefficientPower,
  ``CoreAnchoredComparison.coefficientPower_eq_pow,
  ``CoreAnchoredComparison.exponent_mul_units,
  ``CoreAnchoredComparison.cross_difference_dvd_of_unit_corrected_classes,
  ``CoreAnchoredComparison.principal_eq_of_unit_corrected_anchored_classes,
  ``CoreAnchoredComparison.cross_difference_dvd_of_classes,
  ``CoreAnchoredComparison.exponent_sub_dvd_of_anchored_classes,
  ``CoreAnchoredComparison.principal_eq_of_anchored_classes_and_bound,
  ``CoreAnchoredComparison.principal_eq_of_anchored_tower,
  ``CoreAnchoredComparison.exponent_eq_of_principal_eq,
  ``CoreAnchoredComparison.unanchored_unit_power_fails,
  ``CoreAnchoredComparison.quadratic_label_bound,
  ``CoreAnchoredDecomposition.residue_kummer_pow_of_reduced_comparison
]

private def uniqueAnchoredNames (names : Array Name) : Array Name :=
  names.foldl (fun acc name => if acc.contains name then acc else acc.push name) #[]

private def anchoredDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    dependencies := dependencies ++ value.getUsedConstants
  return uniqueAnchoredNames dependencies

private def anchoredKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def anchoredModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "<no-module-index>"
  | some idx => env.header.moduleNames[idx]!.toString

private partial def collectAnchoredClosure (env : Environment) (ownerModule : ModuleIdx)
    (todo : List Name) (seen : NameSet := {}) (ordered : Array Name := #[]) : Array Name :=
  match todo with
  | [] => ordered
  | name :: rest =>
    if seen.contains name then
      collectAnchoredClosure env ownerModule rest seen ordered
    else
      let seen := seen.insert name
      if env.getModuleIdxFor? name != some ownerModule then
        collectAnchoredClosure env ownerModule rest seen ordered
      else
        match env.find? name with
        | none => collectAnchoredClosure env ownerModule rest seen ordered
        | some info =>
          let dependencies := anchoredDependencies info
          collectAnchoredClosure env ownerModule (dependencies.toList ++ rest)
            seen (ordered.push name)

elab "#export_anchored_comparison" : command => do
  let env ← getEnv
  let some ownerModule := env.getModuleIdxFor? ``CoreAnchoredComparison.dvd_determinant
    | throwError "Boundary.AnchoredComparison module index was not found"
  for name in anchoredRequestedNames do
    unless (env.find? name).isSome do
      throwError "selected declaration was not found: {name}"
  let localNames := collectAnchoredClosure env ownerModule anchoredRequestedNames.toList
  let json ← liftTermElabM do
    let mut nodes := #[]
    for name in localNames do
      let some info := (← getEnv).find? name
        | throwError "local declaration disappeared from environment: {name}"
      let statement ← ppExpr info.type
      let constants := (anchoredDependencies info).map fun dependency =>
        toJson dependency.toString
      nodes := nodes.push <| Json.mkObj [
        ("id", toJson name.toString),
        ("module", toJson (anchoredModuleName (← getEnv) name)),
        ("kind", toJson (anchoredKind info)),
        ("statement", toJson statement.pretty),
        ("constants", Json.arr constants)
      ]
    return Json.arr nodes
  IO.println json.compress

#export_anchored_comparison
