import Lake
open Lake DSL

package «core-kummer»

-- mathlib is resolved through the committed lake-manifest.json.
-- It used to be pinned to one machine's Desktop path, which made every
-- downstream package unbuildable elsewhere.
require mathlib

/-
Roots bookkeeping note (2026-10-24).

Before this edit the package declared only seven roots:

  ContinuousKummerTheory : ContH1.Basic, Hilbert90, Kummer.Basic, Kummer.Equiv
  ValuationSupport       : KummerValuationSeparation
  CoreKummer             : KummerClassValuationBridge, CohomologyReflection

while the package actually contains 30 Lean modules. The other twenty-three
(Boundary/*, the remaining ContinuousKummerTheory modules, TateCurvesTheta/*,
Export*.lean) were therefore *orphans*: `lake build` never compiled them, they
had no `.olean`, and any file importing them failed with
"object file ... does not exist". That is exactly why
`Boundary/DecompositionBridge.lean` could not be checked by an elaborator
(recorded as A21 in delegated/2026-10-24/T008/). The fix is to list every
module as a root, so a from-scratch build covers the whole package.

No source file, statement or proof is changed by this edit. Only the build
graph is made complete.
-/

lean_lib ContinuousKummerTheory where
  roots := #[`ContinuousKummerTheory.ContH1.Basic,
    `ContinuousKummerTheory.ContH1.Corestriction,
    `ContinuousKummerTheory.Hilbert90,
    `ContinuousKummerTheory.Kummer.Basic,
    `ContinuousKummerTheory.Kummer.Corestriction,
    `ContinuousKummerTheory.Kummer.Decomposition,
    `ContinuousKummerTheory.Kummer.DecompositionSurjective,
    `ContinuousKummerTheory.Kummer.Equiv,
    `ContinuousKummerTheory.Kummer.Restriction,
    `ContinuousKummerTheory.Kummer.Specialization,
    `ContinuousKummerTheory.Kummer.Values]
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib ValuationSupport where
  srcDir := "../core-local-global"
  roots := #[`KummerValuationSeparation]
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib TateCurvesTheta where
  roots := #[`TateCurvesTheta.QParameter.Basic,
    `TateCurvesTheta.Theta.Basic,
    `TateCurvesTheta.Theta.Periodicity,
    `TateCurvesTheta.Kummer.ThetaGermCore]
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib Boundary where
  roots := #[`Boundary.AnchoredComparison,
    `Boundary.DecompositionBridge,
    `Boundary.DiscreteValuation,
    `Boundary.FinitePlace,
    `Boundary.Frontier,
    `Boundary.LaurentPoint,
    `Boundary.PrecisionLoss,
    `Boundary.ProjectiveComparison,
    `Boundary.ReducedComparison,
    `Boundary.ThetaGermTransport]
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib Export where
  roots := #[`ExportAnchoredComparison,
    `ExportFrontier,
    `ExportProjectiveComparison,
    `ExportThetaGermTransport]
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib CoreKummer where
  roots := #[`KummerClassValuationBridge, `CohomologyReflection]
  moreLeanArgs := #["-DwarningAsError=true"]
