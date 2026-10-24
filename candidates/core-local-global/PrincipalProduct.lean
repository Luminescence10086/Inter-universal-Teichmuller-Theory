import ResidueHull
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Finite products of principal ideal rings: a full-coordinate witness forces
nonvanishing components of a principal ideal generator. These are algebraic
statements, not an identification of an IUT coefficient ring. -/
set_option autoImplicit false
open Set

namespace CorePrincipalProduct

noncomputable section
variable {ι : Type*} [Finite ι] {R : ι → Type*}
  [∀ i, CommRing (R i)] [∀ i, IsPrincipalIdealRing (R i)]

/-- A principal generator in the actual product coefficient ring. -/
def generator (I : Ideal (Π i, R i)) : Π i, R i := Submodule.IsPrincipal.generator I

theorem span_generator (I : Ideal (Π i, R i)) :
    Ideal.span ({generator I} : Set (Π i, R i)) = I :=
  Ideal.span_singleton_generator I

/-- A single member with nonzero coordinates suffices; no measure premise is
used to manufacture nonvanishing. -/
theorem generator_components_ne_zero (I : Ideal (Π i, R i))
    (a : Π i, R i) (ha : a ∈ I) (hne : ∀ i, a i ≠ 0) :
    ∀ i, generator I i ≠ 0 := by
  obtain ⟨b, hb⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp ha
  intro i hi
  have heq := congrFun hb i
  change a i = generator I i * b i at heq
  rw [hi, zero_mul] at heq
  exact hne i heq

/-- The carrier is exactly lambda times the coefficient ring. -/
theorem carrier_eq_generator_image (I : Ideal (Π i, R i)) :
    (I : Set (Π i, R i)) = (fun x => generator I * x) '' Set.univ := by
  ext x
  change x ∈ I ↔ _
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hx
    exact ⟨b, Set.mem_univ b, hb.symm⟩
  · rintro ⟨b, _, hb⟩
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mpr ⟨b, hb.symm⟩

/-- This formulation exposes the nonzero-coordinate and shape obligations
jointly, instead of assuming the desired admissible shape as an input. -/
theorem exists_full_principal_shape (I : Ideal (Π i, R i))
    (a : Π i, R i) (ha : a ∈ I) (hne : ∀ i, a i ≠ 0) :
    ∃ lam : Π i, R i, (∀ i, lam i ≠ 0) ∧
      (I : Set (Π i, R i)) = (fun x => lam * x) '' Set.univ :=
  ⟨generator I, generator_components_ne_zero I a ha hne, carrier_eq_generator_image I⟩

end
end CorePrincipalProduct

#print axioms CorePrincipalProduct.span_generator
#print axioms CorePrincipalProduct.generator_components_ne_zero
#print axioms CorePrincipalProduct.carrier_eq_generator_image
#print axioms CorePrincipalProduct.exists_full_principal_shape
