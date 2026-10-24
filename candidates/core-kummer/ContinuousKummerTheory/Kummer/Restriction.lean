/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Equiv

/-!
# Restriction and the Kummer map

Let `L/K` be an extension of fields, `Ω_K/K` a normal extension and `Ω_L/L` an algebraic
extension, together with a `K`-embedding `Ω_K → Ω_L` (encoded as an `Algebra Ω_K Ω_L` instance
with `IsScalarTower K Ω_K Ω_L`). Restricting automorphisms gives a continuous homomorphism
`Gal(Ω_L/L) → Gal(Ω_K/K)` (`KummerTheory.galRestrict`), and hence a restriction map

`ContH1 Gal(Ω_K/K) (Mu n Ω_K) → ContH1 Gal(Ω_L/L) (Mu n Ω_L)`.

We show that the Kummer map is compatible with restriction: `res (κ_K a) = κ_L a`
(`KummerTheory.restriction_kummer`). No finiteness of `L/K` is needed; the typical example is
`Ω_K` (resp. `Ω_L`) a separable closure of `K` (resp. `L`).
-/

open groupCohomology IntermediateField

namespace KummerTheory

variable (K L ΩK ΩL : Type*) [Field K] [Field L] [Field ΩK] [Field ΩL]
  [Algebra K L] [Algebra K ΩK] [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL]
  [Algebra ΩK ΩL] [IsScalarTower K ΩK ΩL] [Normal K ΩK]

/-- The restriction homomorphism `Gal(Ω_L/L) → Gal(Ω_K/K)`. -/
noncomputable def galRestrict : Gal(ΩL/L) →* Gal(ΩK/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := ΩL) ΩK).comp (AlgEquiv.restrictScalarsHom K)

variable {K L ΩK ΩL}

@[simp]
theorem algebraMap_galRestrict_apply (σ : Gal(ΩL/L)) (x : ΩK) :
    algebraMap ΩK ΩL (galRestrict K L ΩK ΩL σ x) = σ (algebraMap ΩK ΩL x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) ΩK x

variable (K L ΩK ΩL) in
open scoped Topology in
theorem continuous_galRestrict [Algebra.IsIntegral L ΩL] :
    Continuous (galRestrict K L ΩK ΩL) := by
  refine continuous_of_continuousAt_one _ ?_
  intro V hV
  rw [map_one] at hV
  obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff K ΩK V).1 hV
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.1 (E.fg_of_fg_toSubalgebra
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE)))
  have hmem : (⋂ x ∈ t, (MulAction.stabilizer Gal(ΩL/L) (algebraMap ΩK ΩL x) : Set Gal(ΩL/L)))
      ∈ 𝓝 (1 : Gal(ΩL/L)) :=
    (Filter.biInter_mem htfin).2 fun x _ =>
      (stabilizer_isOpen_of_isIntegral (algebraMap ΩK ΩL x)).mem_nhds (by simp)
  refine Filter.mem_map.2 (Filter.mem_of_superset hmem fun σ hσ => hEV ?_)
  simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hadj]
  have := (forall_mem_adjoin_smul_eq_self_iff K (S := t) (galRestrict K L ΩK ΩL σ)).2
    fun x hx => (algebraMap ΩK ΩL).injective (by
      rw [AlgEquiv.smul_def, algebraMap_galRestrict_apply]
      exact hσ x hx)
  exact this

variable (n : ℕ)

/-- The map `μ_n(Ω_K) → μ_n(Ω_L)` induced by the embedding `Ω_K → Ω_L`. -/
def muMap (n : ℕ) (Ω Ω' : Type*) [Field Ω] [Field Ω'] [Algebra Ω Ω'] : Mu n Ω →* Mu n Ω' where
  toFun ζ := Mu.mk (Units.map (algebraMap Ω Ω' : Ω →* Ω') (Mu.val ζ))
    (by rw [← map_pow, Mu.val_pow_n, map_one])
  map_one' := Mu.ext (by simp)
  map_mul' _ _ := Mu.ext (by simp)

@[simp]
theorem val_muMap (n : ℕ) {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra Ω Ω'] (ζ : Mu n Ω) :
    Mu.val (muMap n Ω Ω' ζ) = Units.map (algebraMap Ω Ω' : Ω →* Ω') (Mu.val ζ) := rfl

theorem muMap_galRestrict_smul (σ : Gal(ΩL/L)) (ζ : Mu n ΩK) :
    muMap n ΩK ΩL (galRestrict K L ΩK ΩL σ • ζ) = σ • muMap n ΩK ΩL ζ := by
  apply Mu.ext
  ext
  simp [AlgEquiv.smul_units_def]

variable [Algebra.IsIntegral L ΩL]

variable (K L ΩK ΩL) in
/-- The restriction map `H¹_cont(Gal(Ω_K/K), μ_n) → H¹_cont(Gal(Ω_L/L), μ_n)`. -/
noncomputable def restriction :
    ContH1 Gal(ΩK/K) (Mu n ΩK) →* ContH1 Gal(ΩL/L) (Mu n ΩL) :=
  ContH1.map (galRestrict K L ΩK ΩL) (continuous_galRestrict K L ΩK ΩL) (muMap n ΩK ΩL)
    continuous_of_discreteTopology (muMap_galRestrict_smul n)

/-- **Kummer theory is compatible with restriction**: the restriction of the Kummer class of
`a ∈ Kˣ` is the Kummer class of the image of `a` in `Lˣ`. -/
theorem restriction_kummer [Algebra.IsIntegral K ΩK] [HasKummerRoots n K ΩK]
    [HasKummerRoots n L ΩL] (a : Kˣ) :
    restriction K L ΩK ΩL n (kummer n K ΩK a) =
      kummer n L ΩL (Units.map (algebraMap K L : K →* L) a) := by
  set α := kummerRoot n K ΩK a
  have hα := kummerRoot_pow n K ΩK a
  have hα' : Units.map (algebraMap ΩK ΩL : ΩK →* ΩL) α ^ n =
      Units.map (algebraMap L ΩL : L →* ΩL) (Units.map (algebraMap K L : K →* L) a) := by
    rw [← map_pow, hα]
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [kummer_eq a α hα, kummer_eq _ _ hα', restriction, ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext σ
  apply Mu.ext
  ext
  simp [AlgEquiv.smul_units_def]

/-- The restriction map on `Kˣ/(Kˣ)ⁿ`, compatible with `kummerEquiv`. -/
theorem restriction_kummerEquiv [IsGalois K ΩK] [IsGalois L ΩL] [HasKummerRoots n K ΩK]
    [HasKummerRoots n L ΩL] (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    restriction K L ΩK ΩL n (kummerEquiv n K ΩK x) =
      kummerEquiv n L ΩL (QuotientGroup.map _ _ (Units.map (algebraMap K L : K →* L))
        (by rintro _ ⟨b, rfl⟩; exact ⟨Units.map (algebraMap K L : K →* L) b, by simp⟩) x) := by
  induction x using QuotientGroup.induction_on with
  | H a => exact restriction_kummer n a

end KummerTheory
