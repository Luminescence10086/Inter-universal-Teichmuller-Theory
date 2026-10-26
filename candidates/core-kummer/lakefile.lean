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
    `TateCurvesTheta.Analysis.UltrametricSum,
    `TateCurvesTheta.Analysis.MaxTerm,
    `TateCurvesTheta.Analysis.Strassmann,
    `TateCurvesTheta.Analysis.StrassmannSphere,
    `TateCurvesTheta.Theta.Basic,
    `TateCurvesTheta.Theta.Periodicity,
    `TateCurvesTheta.Theta.Product,
    `TateCurvesTheta.Theta.QBinomial,
    `TateCurvesTheta.Theta.FactorSeries,
    `TateCurvesTheta.Theta.Divisor,
    `TateCurvesTheta.Theta.Uniqueness,
    `TateCurvesTheta.Theta.ThetaProdLaurent,
    `TateCurvesTheta.Theta.ThetaProdGlobalLaurent,
    `TateCurvesTheta.Theta.LaurentSphere,
    `TateCurvesTheta.Theta.LaurentSphereReduce,
    `TateCurvesTheta.Theta.LaurentUnitSphere,
    `TateCurvesTheta.Theta.Normalization,
    `TateCurvesTheta.Theta.Durfee,
    `TateCurvesTheta.Theta.PuncturedProduct,
    `TateCurvesTheta.Theta.WeightSpace,
    `TateCurvesTheta.Theta.AuditTripleProduct,
    `TateCurvesTheta.AnalyticQuotient,
    `TateCurvesTheta.Arithmetic.DivisorConvolution,
    `TateCurvesTheta.QParameter.BaseChange,
    `TateCurvesTheta.TateCurve.A6Series,
    `TateCurvesTheta.TateCurve.AbelStep,
    `TateCurvesTheta.TateCurve.AdditionLaw,
    `TateCurvesTheta.TateCurve.CoordinateAnnulusLaurent,
    `TateCurvesTheta.TateCurve.CoordinateAnnulusLaurentY,
    `TateCurvesTheta.TateCurve.CoordinateBaseChange,
    `TateCurvesTheta.TateCurve.CoordinateExpansion,
    `TateCurvesTheta.TateCurve.CoordinateInversion,
    `TateCurvesTheta.TateCurve.DefectAnnulusLaurent,
    `TateCurvesTheta.TateCurve.DefectCoeffBaseChange,
    `TateCurvesTheta.TateCurve.DefectVanishing,
    `TateCurvesTheta.TateCurve.Discriminant,
    `TateCurvesTheta.TateCurve.EisensteinKernels,
    `TateCurvesTheta.TateCurve.EisensteinSeries,
    `TateCurvesTheta.TateCurve.GroupLaw,
    `TateCurvesTheta.TateCurve.IntegralModel,
    `TateCurvesTheta.TateCurve.JInvariant,
    `TateCurvesTheta.TateCurve.LargePointParametrization,
    `TateCurvesTheta.TateCurve.Parametrization,
    `TateCurvesTheta.TateCurve.PointMap,
    `TateCurvesTheta.TateCurve.Quotient,
    `TateCurvesTheta.TateCurve.SphereBounds,
    `TateCurvesTheta.TateCurve.SplitReduction,
    `TateCurvesTheta.TateCurve.SurjectivityAnnulus,
    `TateCurvesTheta.TateCurve.SurjectivitySphere,
    `TateCurvesTheta.TateCurve.TatePointMem,
    `TateCurvesTheta.TateCurve.TatePointOnCurve,
    `TateCurvesTheta.TateCurve.TateUniformization,
    `TateCurvesTheta.TateCurve.Weierstrass,
    `TateCurvesTheta.TateCurve.WeierstrassIdentity,
    `TateCurvesTheta.Kummer.ThetaGermCore]
  moreLeanArgs := #["-DwarningAsError=true", "-Dlinter.style.haveILetI=false"]

lean_lib Boundary where
  roots := #[`Boundary.AnchoredComparison,
    `Boundary.AnnularConvergence,
    `Boundary.AnnularOverlap,
    `Boundary.AnnularThetaDescent,
    `Boundary.DecompositionBridge,
    `Boundary.DiscreteValuation,
    `Boundary.FinitePlace,
    `Boundary.Frontier,
    `Boundary.GlobalThetaRigidity,
    `Boundary.KummerDoubleCover,
    `Boundary.LaurentPoint,
    `Boundary.LocalDeckSynchronization,
    `Boundary.PrecisionLoss,
    `Boundary.PrimitiveDeck,
    `Boundary.ProjectiveComparison,
    `Boundary.ReducedComparison,
    `Boundary.SphereCoefficientDescent,
    `Boundary.SphereNonvanishing,
    `Boundary.ThetaGermTransport,
    `Boundary.TwistedThetaCurvature]
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
