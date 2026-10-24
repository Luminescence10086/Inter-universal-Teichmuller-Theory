import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.ZMod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! Finite residue cylinders of actual p-adic integers, with normalized additive
Haar measure. This module makes no assertion about an IUT realization. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace CoreResidueHaar

section FiniteQuotient
variable {G F : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
  [AddGroup F] [Fintype F] [DecidableEq F]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
  (f : G →+ F) (hsurj : Function.Surjective f)
  (hmeas : ∀ a, MeasurableSet (f ⁻¹' {a}))

include hsurj in
omit [Fintype F] [DecidableEq F] [IsProbabilityMeasure μ] in
/-- Surjectivity and translation invariance force all finite quotient fibers
  to have equal mass. There is no assumed volume formula in the hypotheses. -/
theorem fiber_measure_eq (a : F) : μ (f ⁻¹' {a}) = μ (f ⁻¹' {0}) := by
  obtain ⟨b, hb⟩ := hsurj a
  have ht : (fun x : G => b + x) ⁻¹' (f ⁻¹' {a}) = f ⁻¹' {0} := by
    ext x
    simp [Set.mem_preimage, Set.mem_singleton_iff, map_add, ← hb]
  rw [← measure_preimage_add μ b (f ⁻¹' {a}), ht]

include hsurj hmeas in
omit [DecidableEq F] in
/-- Exact finite quotient count divided by the quotient size, for every
  probability translation invariant measure and every measurable finite quotient. -/
theorem cylinder_measure (s : Finset F) :
    μ (f ⁻¹' (s : Set F)) = (s.card : ℝ≥0∞) / Fintype.card F := by
  have hzero : μ (f ⁻¹' {0}) = (1 : ℝ≥0∞) / Fintype.card F := by
    apply (ENNReal.eq_div_iff (by exact_mod_cast Fintype.card_ne_zero)
      (by simp)).mpr
    have hsum := sum_measure_preimage_singleton (μ := μ) (f := f) Finset.univ
      (fun a _ => hmeas a)
    simpa only [fiber_measure_eq μ f hsurj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.coe_univ, Set.preimage_univ, measure_univ] using hsum
  rw [← sum_measure_preimage_singleton s (fun a _ => hmeas a)]
  simp_rw [fiber_measure_eq μ f hsurj, hzero]
  simp [nsmul_eq_mul, div_eq_mul_inv]
end FiniteQuotient

variable (p : ℕ) [Fact p.Prime]

/-- Continuity is proved from closed fibers, using the actual kernel of
  p-adic reduction, rather than postulated for a model map. -/
theorem continuous_reduction (k : ℕ) :
    Continuous (PadicInt.toZModPow (p := p) k) := by
  have h0 : IsClosed ((PadicInt.toZModPow (p := p) k) ⁻¹' ({0} : Set (ZMod (p ^ k)))) := by
    have heq : (PadicInt.toZModPow (p := p) k) ⁻¹' ({0} : Set (ZMod (p ^ k))) =
        {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-k : ℤ)} := by
      ext x
      change PadicInt.toZModPow k x = 0 ↔ _
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow,
        ← PadicInt.norm_le_pow_iff_mem_span_pow]
      rfl
    rw [heq]
    exact isClosed_le continuous_norm continuous_const
  have hfiber (a : ZMod (p ^ k)) :
      IsClosed ((PadicInt.toZModPow (p := p) k) ⁻¹' ({a} : Set (ZMod (p ^ k)))) := by
    obtain ⟨b, hb⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) k) a
    have heq : (PadicInt.toZModPow (p := p) k) ⁻¹' ({a} : Set (ZMod (p ^ k))) =
        (fun x : ℤ_[p] => x - b) ⁻¹'
          ((PadicInt.toZModPow (p := p) k) ⁻¹' ({0} : Set (ZMod (p ^ k)))) := by
      ext x
      simp [Set.mem_preimage, Set.mem_singleton_iff, map_sub, ← hb, sub_eq_zero]
    rw [heq]
    exact h0.preimage (continuous_id.sub continuous_const)
  apply continuous_iff_isClosed.mpr
  intro s _
  rw [← Set.biUnion_preimage_singleton]
  exact isClosed_iUnion_of_finite fun a => isClosed_iUnion_of_finite fun _ => hfiber a

noncomputable section

instance padicMeasurableSpace : MeasurableSpace ℤ_[p] := borel _
instance padicBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

variable (ι : Type*) [Fintype ι]

/-- Coordinatewise reduction is a ring homomorphism, not just a finite label map. -/
def reduction (k : ℕ) : (ι → ℤ_[p]) →+* (ι → ZMod (p ^ k)) where
  toFun x i := PadicInt.toZModPow k (x i)
  map_one' := by ext i; simp
  map_mul' x y := by ext i; simp
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype ι] in
theorem reduction_surjective (k : ℕ) :
    Function.Surjective (reduction p ι k) := by
  exact Function.Surjective.piMap (fun _ =>
    ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) k))

omit [Fintype ι] in
theorem reduction_continuous (k : ℕ) : Continuous (reduction p ι k) := by
  exact continuous_pi fun i => (continuous_reduction p k).comp (continuous_apply i)

/-- The actual additive Haar measure on the compact standard p-adic lattice,
normalized to give that whole lattice mass one. -/
def latticeHaar : Measure (ι → ℤ_[p]) := Measure.addHaarMeasure ⊤

instance latticeHaar_probability : IsProbabilityMeasure (latticeHaar p ι) where
  measure_univ := by
    exact Measure.addHaarMeasure_self (K₀ := ⊤)

instance latticeHaar_invariant : (latticeHaar p ι).IsAddLeftInvariant :=
  inferInstanceAs (Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts (ι → ℤ_[p]))).IsAddLeftInvariant

instance latticeHaar_isHaar : (latticeHaar p ι).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts (ι → ℤ_[p]))).IsAddHaarMeasure

/-- A finite-level counting certificate computes genuine normalized Haar volume. -/
theorem residue_cylinder_measure (k : ℕ) (s : Finset (ι → ZMod (p ^ k))) :
    latticeHaar p ι (reduction p ι k ⁻¹' (s : Set (ι → ZMod (p ^ k)))) =
      (s.card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  classical
  simpa [Fintype.card_fun] using
    cylinder_measure (latticeHaar p ι) (reduction p ι k).toAddMonoidHom
      (reduction_surjective p ι k)
      (fun a => (reduction_continuous p ι k).measurable (measurableSet_singleton a)) s

end
end CoreResidueHaar

#print axioms CoreResidueHaar.fiber_measure_eq
#print axioms CoreResidueHaar.cylinder_measure
#print axioms CoreResidueHaar.continuous_reduction
#print axioms CoreResidueHaar.reduction_surjective
#print axioms CoreResidueHaar.reduction_continuous
#print axioms CoreResidueHaar.residue_cylinder_measure

