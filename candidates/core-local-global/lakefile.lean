import Lake
open Lake DSL
package «core-local-global»
require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"
@[default_target]
lean_lib CoreLocalGlobal where
  roots := #[`NativeFiber, `IPLCoherence, `Collections, `IntegralScalarOrbit,
    `IntegralMatrixCharacter, `LatticeStabilizer, `SaturationGrowth, `ResidueHaar,
    `PadicSaturation, `ResidueHull, `ResidueModule, `PrincipalProduct, `PadicPrincipalHull,
    `IntegralProductBridge, `IntegralActionDescent, `IntegralActionFrame, `TorsionHullStability]
  moreLeanArgs := #["-DwarningAsError=true"]
