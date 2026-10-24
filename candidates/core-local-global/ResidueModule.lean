import ResidueHaar
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Coefficient-aware finite quotient certificates for module hulls. The ambient
compact additive group need not itself be a ring. Actions need not be linear;
the quotient used to certify the hull must be semilinear over the stated rings. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace CoreResidueModule

section Algebra
variable {R S M N : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  {σ : R →+* S} [RingHomSurjective σ]

/-- The actual coefficient-ring span of a nonempty full cylinder is the
pullback of its finite quotient span, with both coefficient rings explicit. -/
theorem span_cylinder_eq (f : M →ₛₗ[σ] N) (hsurj : Function.Surjective f)
    (s : Set N) (hne : s.Nonempty) :
    Submodule.span R (f ⁻¹' s) = Submodule.comap f (Submodule.span S s) := by
  let I : Submodule R M := Submodule.span R (f ⁻¹' s)
  have hker : f.ker ≤ I := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hb⟩ := hsurj a
    intro x hx
    have hfx : f x = 0 := hx
    have hbI : b ∈ I := Submodule.subset_span (by simpa only [Set.mem_preimage, hb] using ha)
    have hxbI : x + b ∈ I := Submodule.subset_span (by
      simpa only [Set.mem_preimage, map_add, hfx, hb, zero_add] using ha)
    simpa only [add_sub_cancel_right] using I.sub_mem hxbI hbI
  calc
    Submodule.span R (f ⁻¹' s) = Submodule.comap f (Submodule.map f I) :=
      (Submodule.comap_map_eq_self hker).symm
    _ = Submodule.comap f (Submodule.span S s) := by
      dsimp only [I]
      rw [Submodule.map_span, Set.image_preimage_eq s hsurj]
end Algebra

noncomputable section

/-- Carrier of a finite submodule certificate. This is a mathematical finite
carrier, not a claim that arbitrary span membership has an executable solver. -/
def submoduleResidues {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]
    [Fintype N] (J : Submodule S N) : Finset N := by
  classical
  exact Finset.univ.filter (fun x => x ∈ J)

theorem coe_submoduleResidues {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]
    [Fintype N] (J : Submodule S N) :
    (submoduleResidues J : Set N) = (J : Set N) := by
  classical
  ext x
  simp [submoduleResidues]

section Measure
variable {R S M N : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  {σ : R →+* S} [MeasurableSpace M] [MeasurableAdd M] [Fintype N]
  (μ : Measure M) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
  (f : M →ₛₗ[σ] N) (hsurj : Function.Surjective f)
  (hmeas : ∀ a, MeasurableSet (f ⁻¹' {a}))

include hsurj hmeas in
/-- Exact volume of the pullback of a finite submodule. -/
theorem comap_measure (J : Submodule S N) :
    μ (Submodule.comap f J : Set M) =
      ((submoduleResidues J).card : ℝ≥0∞) / Fintype.card N := by
  have heq : (Submodule.comap f J : Set M) = f ⁻¹' (submoduleResidues J : Set N) := by
    rw [coe_submoduleResidues]
    rfl
  rw [heq]
  exact CoreResidueHaar.cylinder_measure μ f.toAddMonoidHom hsurj hmeas (submoduleResidues J)

include hsurj hmeas in
/-- A finite quotient submodule cover bounds the actual R-module hull. No
measurability or full-cylinder assumption on A is needed for this upper bound. -/
theorem hull_measure_le_of_residue_cover (A : Set M) (J : Submodule S N)
    (hcover : ∀ x ∈ A, f x ∈ J) :
    μ (Submodule.span R A : Set M) ≤
      ((submoduleResidues J).card : ℝ≥0∞) / Fintype.card N := by
  have hle : Submodule.span R A ≤ Submodule.comap f J := Submodule.span_le.mpr hcover
  calc
    μ (Submodule.span R A : Set M) ≤ μ (Submodule.comap f J : Set M) := measure_mono hle
    _ = _ := comap_measure μ f hsurj hmeas J

include hsurj hmeas in
/-- The analytic logarithmic bound needs positive actual hull volume. The
finite cover alone gives an upper bound and does not justify dropping this
hypothesis, since Real.log 0 is defined as zero. -/
theorem log_hull_measure_le (A : Set M) (J : Submodule S N)
    (hcover : ∀ x ∈ A, f x ∈ J)
    (hpos : 0 < μ.real (Submodule.span R A : Set M)) :
    Real.log (μ.real (Submodule.span R A : Set M)) ≤
      Real.log (((submoduleResidues J).card : ℝ) / Fintype.card N) := by
  apply Real.log_le_log hpos
  have hcard : (Fintype.card N : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hle := ENNReal.toReal_mono
    (ENNReal.div_ne_top (by simp) hcard)
    (hull_measure_le_of_residue_cover μ f hsurj hmeas A J hcover)
  simpa [Measure.real, ENNReal.toReal_div] using hle

include hsurj hmeas in
/-- A single finite coefficient-module certificate bounds the hull of an entire
possibly infinite family of allowed images. The commutation witness uses the
same quotient f for every action; no zero-growth assumption is made. -/
theorem saturation_hull_measure_le {T : Type*}
    (A : Set M) (s : Set N) (u : T → M → M) (v : T → N → N)
    (hcomm : ∀ i x, f (u i x) = v i (f x))
    (hA : ∀ x ∈ A, f x ∈ s) (J : Submodule S N)
    (hcover : ∀ i a, a ∈ s → v i a ∈ J) :
    μ (Submodule.span R (⋃ i, u i '' A) : Set M) ≤
      ((submoduleResidues J).card : ℝ≥0∞) / Fintype.card N := by
  apply hull_measure_le_of_residue_cover μ f hsurj hmeas (⋃ i, u i '' A) J
  intro y hy
  obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
  rw [hcomm]
  exact hcover i (f x) (hA x hx)

include hsurj hmeas in
/-- For nonempty full cylinders the finite quotient certificate is exact. -/
theorem quotient_hull_measure [RingHomSurjective σ] (s : Finset N) (hne : s.Nonempty) :
    μ (Submodule.span R (f ⁻¹' (s : Set N)) : Set M) =
      ((submoduleResidues (Submodule.span S (s : Set N))).card : ℝ≥0∞) / Fintype.card N := by
  rw [span_cylinder_eq f hsurj (s : Set N) hne.to_set]
  exact comap_measure μ f hsurj hmeas (Submodule.span S (s : Set N))
end Measure

/-- An actual semilinear finite quotient of the standard p-adic lattice. -/
def padicReduction (p : ℕ) [Fact p.Prime] (ι : Type*) (k : ℕ) :
    (ι → ℤ_[p]) →ₛₗ[PadicInt.toZModPow (p := p) k] (ι → ZMod (p ^ k)) where
  toFun := CoreResidueHaar.reduction p ι k
  map_add' := (CoreResidueHaar.reduction p ι k).map_add
  map_smul' r x := by
    ext i
    exact map_mul (PadicInt.toZModPow (p := p) k) r (x i)

/-- Genuine Z_p-module hull volumes are certified by their finite
Z/(p^k)-module hull, retaining the coefficient reduction explicitly. -/
theorem padic_module_hull_measure (p : ℕ) [Fact p.Prime]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ)
    (s : Finset (ι → ZMod (p ^ k))) (hne : s.Nonempty) :
    CoreResidueHaar.latticeHaar p ι
      (Submodule.span ℤ_[p] (padicReduction p ι k ⁻¹' (s : Set (ι → ZMod (p ^ k)))) :
        Set (ι → ℤ_[p])) =
      ((submoduleResidues (Submodule.span (ZMod (p ^ k)) (s : Set (ι → ZMod (p ^ k))))).card :
        ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  classical
  let : RingHomSurjective (PadicInt.toZModPow (p := p) k) :=
    ⟨ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) k)⟩
  simpa [Fintype.card_fun] using quotient_hull_measure
    (CoreResidueHaar.latticeHaar p ι) (padicReduction p ι k)
    (CoreResidueHaar.reduction_surjective p ι k)
    (fun a => (CoreResidueHaar.reduction_continuous p ι k).measurable
      (measurableSet_singleton a)) s hne
end
end CoreResidueModule

#print axioms CoreResidueModule.span_cylinder_eq
#print axioms CoreResidueModule.coe_submoduleResidues
#print axioms CoreResidueModule.comap_measure
#print axioms CoreResidueModule.hull_measure_le_of_residue_cover
#print axioms CoreResidueModule.log_hull_measure_le
#print axioms CoreResidueModule.saturation_hull_measure_le
#print axioms CoreResidueModule.quotient_hull_measure
#print axioms CoreResidueModule.padic_module_hull_measure

