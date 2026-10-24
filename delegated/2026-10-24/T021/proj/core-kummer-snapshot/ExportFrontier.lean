import Lean
import Boundary.Frontier

open Lean Elab Command Meta

private def frontierRequestedNames : Array Name := #[
  ``CoreDiscreteKummer.exponent,
  ``CoreDiscreteKummer.exponent_pow,
  ``CoreDiscreteKummer.exponent_sub_dvd_of_power,
  ``CoreDiscreteKummer.exponent_eq_of_bounded_power,
  ``CoreDiscreteKummer.exponent_eq_of_power_tower,
  ``CoreDiscreteKummer.valuation_eq_of_exponent_eq,
  ``CoreDiscreteKummer.integerRegion,
  ``CoreDiscreteKummer.mem_principal_iff,
  ``CoreDiscreteKummer.principal_eq_of_exponent_eq,
  ``CoreDiscreteKummer.power_ratio_of_kummer_eq,
  ``CoreDiscreteKummer.principal_eq_of_kummer_eq_and_bound,
  ``CoreDiscreteKummer.principal_eq_of_normalized_kummer_tower,
  ``CoreFinitePlaceKummer.fieldAt,
  ``CoreFinitePlaceKummer.localValuation,
  ``CoreFinitePlaceKummer.integerRegion_eq,
  ``CoreFinitePlaceKummer.integerRing_isDVR,
  ``CoreFinitePlaceKummer.mem_principal_iff,
  ``CoreFinitePlaceKummer.principal_eq_of_normalized_kummer_tower,
  ``CoreReducedComparison.pullback_injective,
  ``CoreReducedComparison.residue_classes_eq_of_specialization_squares,
  ``CoreKummerPrecision.exponent_sub_dvd_of_raised_level,
  ``CoreKummerPrecision.principal_eq_of_raised_level_and_bound,
  ``KummerTheory.Decomposition.decompositionMap_surjective,
  ``CoreDecompositionBridge.reducedClass,
  ``CoreDecompositionBridge.residue_kummer_eq_of_reduced_restrictions_eq,
  ``CoreDecompositionBridge.principal_eq_of_reduced_comparison_and_bound,
  ``CoreLaurentPoint.constants_compatible,
  ``CoreLaurentPoint.constantsAlgebra,
  ``CoreLaurentPoint.constantsSMul,
  ``CoreLaurentPoint.coefficientAlgebra,
  ``CoreLaurentPoint.coefficientTower,
  ``CoreLaurentPoint.residue_powerSeries,
  ``CoreLaurentPoint.comap_eq_powerSeries_valuationSubring,
  ``CoreLaurentPoint.rational_residues,
  ``CoreLaurentPoint.decompositionMap_surjective_at_germ,
  ``CoreLaurentPoint.principal_eq_of_powerSeries_comparison
]

private def uniqueNames (names : Array Name) : Array Name :=
  names.foldl (fun acc name => if acc.contains name then acc else acc.push name) #[]

private def constantDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    dependencies := dependencies ++ value.getUsedConstants
  return uniqueNames dependencies

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | none => "<no-module-index>"
  | some idx => env.header.moduleNames[idx]!.toString

private partial def collectFrontierClosure (env : Environment) (frontierModule : ModuleIdx)
    (todo : List Name) (seen : NameSet := {}) (ordered : Array Name := #[]) : Array Name :=
  match todo with
  | [] => ordered
  | name :: rest =>
    if seen.contains name then
      collectFrontierClosure env frontierModule rest seen ordered
    else
      let seen := seen.insert name
      if env.getModuleIdxFor? name != some frontierModule then
        collectFrontierClosure env frontierModule rest seen ordered
      else
        match env.find? name with
        | none => collectFrontierClosure env frontierModule rest seen ordered
        | some info =>
          let dependencies := constantDependencies info
          collectFrontierClosure env frontierModule (dependencies.toList ++ rest)
            seen (ordered.push name)

elab "#export_frontier" : command => do
  let env ← getEnv
  let some frontierModule := env.getModuleIdxFor? ``CoreDiscreteKummer.exponent
    | throwError "Boundary.Frontier module index was not found"
  for name in frontierRequestedNames do
    unless (env.find? name).isSome do
      throwError "selected declaration was not found: {name}"
  let localNames := collectFrontierClosure env frontierModule frontierRequestedNames.toList
  let externalNames := frontierRequestedNames.filter fun name =>
    env.getModuleIdxFor? name != some frontierModule
  let nodeJson ← liftTermElabM do
    let mut nodes := #[]
    for name in localNames do
      let some info := (← getEnv).find? name
        | throwError "local declaration disappeared from environment: {name}"
      let statement ← ppExpr info.type
      let constants := (constantDependencies info).map fun dependency =>
        toJson dependency.toString
      nodes := nodes.push <| Json.mkObj [
        ("id", toJson name.toString),
        ("module", toJson (declarationModuleName (← getEnv) name)),
        ("kind", toJson (constantKind info)),
        ("statement", toJson statement.pretty),
        ("constants", Json.arr constants)
      ]
    return Json.arr nodes
  let externalJson ← liftTermElabM do
    let mut declarations := #[]
    for name in externalNames do
      let some info := (← getEnv).find? name
        | throwError "external upstream declaration was not found: {name}"
      let statement ← ppExpr info.type
      declarations := declarations.push <| Json.mkObj [
        ("id", toJson name.toString),
        ("module", toJson (declarationModuleName (← getEnv) name)),
        ("kind", toJson (constantKind info)),
        ("statement", toJson statement.pretty)
      ]
    return Json.arr declarations
  IO.println nodeJson.compress
  if !externalNames.isEmpty then
    IO.eprintln s!"UPSTREAM_EXTERNAL_DECLARATIONS={externalJson.compress}"

#export_frontier
