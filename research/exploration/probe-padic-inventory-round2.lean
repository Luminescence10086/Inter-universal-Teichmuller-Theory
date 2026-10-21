/-
Round 2: disambiguate namespaced identifiers and check the type-class gaps.
Run from the MAIN checkout:
  cd 'D:\Inter-universal Teichmüller Theory\bridge'
  lake env lean --json 'D:\iut-wt\x-feas\probe2.lean'
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.DividedPowers.Padic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.Teichmuller
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-! ### type-class gaps -/

#synth Valued ℚ_[p] NNReal
#synth NormedAlgebra ℚ ℚ_[p]
#synth HasSummableGeomSeries ℚ_[p]
#synth NonarchimedeanAddGroup ℚ_[p]
#synth NonarchimedeanRing ℚ_[p]
#synth NonarchimedeanRing ℤ_[p]
#synth IsUltrametricDist ℤ_[p]
#synth CompleteSpace ℤ_[p]
#synth Valued ℂ_[p] NNReal

/-! ### namespaced versions of the ramification API -/

#check @Ideal.IsUnramifiedAt
#check @Algebra.IsUnramifiedAt
#check @Ideal.ramificationIdx'_eq_ramificationIdx
#check @Ideal.ramificationIdx_inertiaDeg_sum
#check @Ideal.sum_ramification_inertia
#check @Ideal.ramificationIdxIn
#check @Ideal.ramificationIdxIn_eq_ramificationIdx
#check @Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
#check @Ideal.ramificationIdx_eq_of_isGaloisGroup
#check @IsDedekindDomain.HeightOneSpectrum.adicAbv
#check @IsDedekindDomain.HeightOneSpectrum.adicCompletion
#check @IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
#check @IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
#check @Valuation.valuationSubring_isDiscreteValuationRing
#check @Valuation.integer
#check @Valuation.valuationSubring
#check @Valuation.Integers
#check @Valuation.valuation_surjective

/-! ### Teichmüller: what actually exists -/

#check @WittVector.teichmuller
#check @Perfection.teichmuller
#check @PadicComplexInt
#check @PadicComplex.valued
#check @PadicAlgCl
#check @Padic.rootsOfUnity

/-! ### binomial / factorial p-divisibility support -/

#check @padicValNat_choose_eq_sub_sum_digits
#check @Nat.Prime.dvd_choose_self
#check @Nat.Prime.dvd_choose_pow
#check @Padic.norm_p_lt_one
#check @Padic.norm_p_zpow
#check @tendsto_pow_atTop_nhds_zero_of_norm_lt_one
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
#check @PadicInt.mem_span_pow_iff_le_valuation
#check @PadicInt.norm_le_pow_iff_le_valuation
