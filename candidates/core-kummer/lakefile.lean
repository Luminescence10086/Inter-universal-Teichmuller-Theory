import Lake
open Lake DSL
package «core-kummer»
require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"

lean_lib ContinuousKummerTheory where
  roots := #[`ContinuousKummerTheory.ContH1.Basic, `ContinuousKummerTheory.Hilbert90,
    `ContinuousKummerTheory.Kummer.Basic, `ContinuousKummerTheory.Kummer.Equiv]
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib ValuationSupport where
  srcDir := "../core-local-global"
  roots := #[`KummerValuationSeparation]
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib CoreKummer where
  roots := #[`KummerClassValuationBridge, `CohomologyReflection]
  moreLeanArgs := #["-DwarningAsError=true"]
