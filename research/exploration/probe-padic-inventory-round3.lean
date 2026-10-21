/-
Round 3: is the missing type-class material constructible in one step, or absent?
  cd 'D:\Inter-universal Teichmüller Theory\bridge'
  lake env lean --json 'D:\iut-wt\x-feas\probe3.lean'
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

#check @NormedField.toValued
#check @IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
#check @IsUltrametricDist.nonarchimedeanAddGroup
#check @ValuativeRel.instNonarchimedeanRing
#check @IsValuativeTopology
#check @Valuation.Compatible
#check @Padic.mulValuation
#check @Valuation.integer
#check @PadicInt.subring
#check @PadicInt.coe_coe
#check @PadicInt.coe_ne_zero
#check @PadicInt.coe_pow
#check @PadicInt.coe_mul
#check @PadicInt.maximalIdeal_eq_span_p
#check @Ideal.Quotient.mk_surjective
#check @ZMod.ringHom_surjective
#check @IsCyclic.exists_generator
#check @IsCyclic (ZMod 5)ˣ
#check @PadicInt.hensels_lemma
