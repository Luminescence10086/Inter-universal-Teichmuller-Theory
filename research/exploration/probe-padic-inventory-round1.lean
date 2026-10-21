/-
Read-only inventory probe for the p-adic / U-invariant bridge feasibility study.
Run from the MAIN checkout (oleans live there):

  cd 'D:\Inter-universal Teichmüller Theory\bridge'
  lake env lean --json 'D:\iut-wt\x-feas\probe.lean'

No `-o` flag is passed, so no olean is written and nothing is modified.
Each `#check` is one probe; the JSON diagnostics carry file:line so the
report can cite exactly which identifier resolved.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.DividedPowers.Padic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-! ## Item 1 — valuation decomposition / Valued / WithVal / Multiplicative ℤ -/

#check @Padic.valuation
#check @Padic.valuation_mul
#check @Padic.valuation_inv
#check @Padic.mulValuation
#check @Padic.norm_eq_zpow_neg_valuation
#check @Padic.norm_eq_zpow_log_mulValuation
#check @Padic.valuation_p
#check @Padic.addValuation
#check @PadicInt.valuation
#check @PadicInt.unitCoeff
#check @PadicInt.unitCoeff_spec
#check @PadicInt.mkUnits
#check @PadicInt.norm_units
#check @PadicInt.isUnit_iff
#check @ValuativeRel
#check @ValuativeRel.valuation
#check @Valued
#check @WithVal
#check @WithVal.equiv
#check @WithVal.val_apply_equiv
#check @Padic.withValRingEquiv
#check @PadicInt.withValIntegersRingEquiv
#check @Multiplicative
#check @Multiplicative.ofAdd
#check @IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero
#check @IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod

-- expected absent (previous round's name probes, now with context)
#check @Padic.unitsEquiv
#check @PadicInt.unitBall
#check @Padic.valued

/-! ## Item 2 — Z_p^× structure, residue field, Teichmüller -/

#check @PadicInt.residueField
#check @PadicInt.toZMod
#check @PadicInt.ker_toZMod
#check @PadicInt.toZModPow
#check @PadicInt.ker_toZModPow
#check @PadicInt.norm_le_pow_iff_mem_span_pow
#check @PadicInt.norm_le_pow_iff_le_valuation
#check @PadicInt.mem_span_pow_iff_le_valuation
#check @PadicInt.maximalIdeal_eq_span_p
#check @IsLocalRing.ResidueField
#check @IsLocalRing.residue
#check @IsLocalRing.surjective_units_map_of_local_ringHom
#check @ValuationSubring.unitGroup
#check @ValuationSubring.principalUnitGroup
#check @ValuationSubring.unitGroupToResidueFieldUnits
#check @ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits
#check @ValuationSubring.principalUnitGroupEquiv
#check @rootsOfUnity
#check @IsPrimitiveRoot
#check @IsPrimitiveRoot.zmodEquivZPowers
#check @WittVector.teichmuller
#check @Perfection.teichmuller
#check @PadicInt.teichmuller

#synth IsDiscreteValuationRing ℤ_[p]
#synth IsLocalRing ℤ_[p]
#synth ValuativeRel ℚ_[p]
#synth IsUltrametricDist ℚ_[p]
#synth NormedField ℚ_[p]
#synth Valued ℚ_[p] ℝ≥0
#synth ValuationRing ℤ_[p]

/-! ## Item 3 — p-adic log / exp and the convergence toolkit -/

#check @Padic.log
#check @Padic.exp
#check @PadicInt.log
#check @PadicInt.exp
#check @Padic.logP
#check @LubinTate

#check @PadicInt.dividedPowers
#check @Padic.nonarchimedean
#check @PadicInt.nonarchimedean
#check @Padic.norm_add_eq_max_of_ne
#check @PadicInt.norm_add_eq_max_of_ne
#check @Padic.norm_le_pow_iff_norm_lt_pow_add_one
#check @padicValNat_choose
#check @padicValNat_factorial
#check @padicValNat_factorial_lt_of_ne_zero
#check @NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero
#check @NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one
#check @HasSum.mul_of_nonarchimedean
#check @summable_geometric_of_norm_lt_one
#check @hasSum_geometric_of_norm_lt_one
#check @NormedSpace.exp
#check @NormedSpace.expSeries_div_hasSum_exp

#synth NonarchimedeanRing ℚ_[p]
#synth CompleteSpace ℚ_[p]

/-! ## Item 4 — Kummer theory -/

#check @isCyclic_tfae
#check @autEquivRootsOfUnity
#check @autEquivZmod
#check @autAdjoinRootXPowSubCEquiv
#check @X_pow_sub_C_irreducible_iff_of_odd
#check @rootsOfUnityEquivOfPrimitiveRoots
#check @KummerTheory
#check @IsKummerExtension
#check @KummerDedekind
#check @IsDedekindDomain.selmerGroup
#check @IsDedekindDomain.HeightOneSpectrum.adicCompletion

/-! ## Item 5 — ramification / filtration -/

#check @Valuation
#check @ValuationRing
#check @ValuationSubring
#check @IsDiscreteValuationRing
#check @Ideal.ramificationIdx
#check @Ideal.ramificationIdx'
#check @Ideal.ramificationIdxIn
#check @Ideal.inertiaDeg
#check @Ideal.inertiaDeg'
#check @Ideal.ramificationIdx_def
#check @ramificationIdx'_eq_ramificationIdx
#check @IsDiscreteValuationRing.addVal
#check @IsDiscreteValuationRing.addVal_le_iff_dvd
#check @IsDiscreteValuationRing.idealOrderIsoENat
#check @Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
#check @Valuation.IsUniformizer
#check @Valuation.IsRankOneDiscrete
#check @HeightOneSpectrum.adicCompletion
#check @HeightOneSpectrum.adicCompletionIntegers
#check @IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
#check @IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver
#check @IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
#check @NumberField.adicAbv
#check @IsUnramifiedAt

-- expected absent
#check @IsRamifiedAt
