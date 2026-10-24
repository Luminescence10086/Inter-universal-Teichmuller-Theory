import CohomologyReflection
import Boundary.DiscreteValuation

/-! Reflection of the residue-side class does not require invertibility of the
coefficient-reduction map on the other side of a specialization square. -/
set_option autoImplicit false

namespace CoreReducedComparison

section Reflection
variable {G H M : Type*}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]

theorem pullback_injective (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ)
    (hcomp : ∀ h m, φ h • m = h • m) :
    Function.Injective (ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp) :=
  CoreCohomologyReflection.map_injective φ hφ hsurj (MulEquiv.refl M) continuous_id hcomp

/-- R may be noninjective. Equality after R reflects the right-side classes
through the separately injective pullback, not through an inverse to R. -/
theorem residue_classes_eq_of_specialization_squares
    (φ : H →* G) (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (hcomp : ∀ h m, φ h • m = h • m)
    {C : Type*} (R : C → ContH1 H M) (c d : C) (a b : ContH1 G M)
    (hc : R c = ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp a)
    (hd : R d = ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp b)
    (hcompare : R c = R d) : a = b := by
  apply pullback_injective φ hφ hsurj hcomp
  exact hc.symm.trans (hcompare.trans hd)

end Reflection

end CoreReducedComparison

#print axioms CoreReducedComparison.pullback_injective
#print axioms CoreReducedComparison.residue_classes_eq_of_specialization_squares
