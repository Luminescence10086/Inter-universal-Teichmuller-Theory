import Lean
import Boundary.ProjectiveComparison

open Lean Elab Command Meta

/-! Mechanical export for the 9 declarations selected by the current
`Boundary.ProjectiveComparison.lean` `#print axioms` list. The graph includes only the
transitive type/value-constant closure owned by that module. -/

private def projectiveRequestedNames : Array Name := #[
  ``CoreProjectiveComparison.dvd_cross_determinant,
  ``CoreProjectiveComparison.cross_determinant_dvd_of_classes,
  ``CoreProjectiveComparison.cross_determinant_eq_zero_of_finite_comparison,
  ``CoreProjectiveComparison.cross_determinant_eq_zero_of_tower,
  ``CoreProjectiveComparison.principal_eq_of_calibrated_cross_determinant,
  ``CoreProjectiveComparison.quadratic_labels_eq_of_cross_determinant,
  ``CoreProjectiveComparison.quadratic_determinant_bound,
  ``CoreProjectiveComparison.quadratic_labels_eq_of_finite_comparison,
  ``CoreProjectiveComparison.unequal_anchors_lose_absolute_scale
]

private def uniqueProjectiveNames (names : Array Name) : Array Name :=
  names.foldl (fun acc name => if acc.contains name then acc else acc.push name) #[]

private def projectiveDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    dependencies := dependencies ++ value.getUsedConstants
  return uniqueProjectiveNames dependencies

private def projectiveKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def projectiveModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "<no-module-index>"
  | some idx => env.header.moduleNames[idx]!.toString

private partial def collectProjectiveClosure (env : Environment) (ownerModule : ModuleIdx)
    (todo : List Name) (seen : NameSet := {}) (ordered : Array Name := #[]) : Array Name :=
  match todo with
  | [] => ordered
  | name :: rest =>
    if seen.contains name then
      collectProjectiveClosure env ownerModule rest seen ordered
    else
      let seen := seen.insert name
      if env.getModuleIdxFor? name != some ownerModule then
        collectProjectiveClosure env ownerModule rest seen ordered
      else
        match env.find? name with
        | none => collectProjectiveClosure env ownerModule rest seen ordered
        | some info =>
          let dependencies := projectiveDependencies info
          collectProjectiveClosure env ownerModule (dependencies.toList ++ rest)
            seen (ordered.push name)

elab "#export_projective_comparison" : command => do
  let env ← getEnv
  let some ownerModule := env.getModuleIdxFor? ``CoreProjectiveComparison.dvd_cross_determinant
    | throwError "Boundary.ProjectiveComparison module index was not found"
  for name in projectiveRequestedNames do
    unless (env.find? name).isSome do
      throwError "selected declaration was not found: {name}"
  let localNames := collectProjectiveClosure env ownerModule projectiveRequestedNames.toList
  let json ← liftTermElabM do
    let mut nodes := #[]
    for name in localNames do
      let some info := (← getEnv).find? name
        | throwError "local declaration disappeared from environment: {name}"
      let statement ← ppExpr info.type
      let constants := (projectiveDependencies info).map fun dependency =>
        toJson dependency.toString
      nodes := nodes.push <| Json.mkObj [
        ("id", toJson name.toString),
        ("module", toJson (projectiveModuleName (← getEnv) name)),
        ("kind", toJson (projectiveKind info)),
        ("statement", toJson statement.pretty),
        ("constants", Json.arr constants)
      ]
    return Json.arr nodes
  IO.println json.compress

#export_projective_comparison
