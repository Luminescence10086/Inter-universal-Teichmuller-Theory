import Lake
open Lake DSL
package «core-local-global»
require mathlib
@[default_target]
lean_lib CoreLocalGlobal where
  roots := #[`NativeFiber, `IPLCoherence, `Collections, `IntegralScalarOrbit,
    `IntegralMatrixCharacter, `LatticeStabilizer, `SaturationGrowth, `ResidueHaar,
    `PadicSaturation, `ResidueHull, `ResidueModule, `PrincipalProduct, `PadicPrincipalHull,
    `IntegralProductBridge, `IntegralActionDescent, `IntegralActionFrame, `TorsionHullStability]
  moreLeanArgs := #["-DwarningAsError=true"]
