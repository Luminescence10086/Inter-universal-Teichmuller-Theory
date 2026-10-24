import ContinuousKummerTheory.ContH1.Basic

/-! A checked reflection criterion for the actual continuous H1 map.
The group map must be surjective and the coefficient map an actual equivalence.
Neither hypothesis is asserted for the original IUT comparison. -/
set_option autoImplicit false

namespace CoreCohomologyReflection
variable {G H M N : Type*}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction H N]

theorem map_injective (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (e : M ≃* N) (he : Continuous e.toMonoidHom)
    (hcomp : ∀ h m, e.toMonoidHom (φ h • m) = h • e.toMonoidHom m) :
    Function.Injective (ContH1.map φ hφ e.toMonoidHom he hcomp) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := ContH1.mk_surjective x
  obtain ⟨d, rfl⟩ := ContH1.mk_surjective y
  rw [ContH1.map_mk, ContH1.map_mk, ContH1.mk_eq_mk_iff] at hxy
  obtain ⟨z, hz⟩ := hxy
  apply (ContH1.mk_eq_mk_iff c d).mpr
  refine ⟨e.symm z, fun g => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj g
  apply e.injective
  change e.toMonoidHom (φ a • e.symm z / e.symm z) =
    e.toMonoidHom (c (φ a) / d (φ a))
  rw [map_div, map_div, hcomp]
  rw [show e.toMonoidHom (e.symm z) = z from e.apply_symm_apply z]
  exact hz a

theorem map_eq_iff (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (e : M ≃* N) (he : Continuous e.toMonoidHom)
    (hcomp : ∀ h m, e.toMonoidHom (φ h • m) = h • e.toMonoidHom m) (x y : ContH1 G M) :
    ContH1.map φ hφ e.toMonoidHom he hcomp x =
      ContH1.map φ hφ e.toMonoidHom he hcomp y ↔ x = y :=
  (map_injective φ hφ hsurj e he hcomp).eq_iff

end CoreCohomologyReflection

#print axioms CoreCohomologyReflection.map_injective
#print axioms CoreCohomologyReflection.map_eq_iff



