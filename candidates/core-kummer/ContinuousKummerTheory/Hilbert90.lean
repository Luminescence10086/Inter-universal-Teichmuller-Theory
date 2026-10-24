/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Hilbert 90 for (possibly infinite) Galois extensions

Mathlib proves Noether's form of Hilbert's Theorem 90 for finite extensions
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`). We extend it to an
arbitrary Galois extension `Ω/K` and *continuous* cocycles: a 1-cocycle
`c : Gal(Ω/K) → Ωˣ` which is trivial on the fixing subgroup of some finite subextension is a
coboundary. Continuity for the discrete topology on `Ωˣ` is the same as this condition.

## Main results

* `KummerTheory.isMulCoboundary₁_of_fixingSubgroup` : Hilbert 90 for cocycles trivial on an
  open subgroup `Gal(Ω/E)`, `E/K` finite.
* `KummerTheory.isMulCoboundary₁_of_eventually_eq_one` : the same with the hypothesis
  that `c = 1` on a neighbourhood of `1` in the Krull topology.
-/

open groupCohomology IntermediateField

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- If a 1-cocycle `c` is trivial on `Gal(Ω/E)` then `c σ` only depends on the restriction of
`σ` to any normal subextension containing `E`. -/
theorem eq_of_restrictNormalHom_eq {c : Gal(Ω/K) → Ωˣ} (hc : IsMulCocycle₁ c)
    {E E' : IntermediateField K Ω} [Normal K E'] (hEE' : E ≤ E')
    (hE : ∀ σ ∈ E.fixingSubgroup, c σ = 1) {σ τ : Gal(Ω/K)}
    (h : AlgEquiv.restrictNormalHom E' σ = AlgEquiv.restrictNormalHom E' τ) : c σ = c τ := by
  have hν : σ⁻¹ * τ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h' := congrArg (fun ρ : Gal(E'/K) => (ρ ⟨x, hEE' hx⟩ : Ω)) h
    simp only [AlgEquiv.restrictNormalHom_apply] at h'
    rw [AlgEquiv.mul_apply, ← h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  calc c σ = σ • c (σ⁻¹ * τ) * c σ := by rw [hE _ hν, smul_one, one_mul]
    _ = c τ := by rw [← hc, mul_inv_cancel_left]

set_option synthInstance.maxHeartbeats 200000 in
-- The instance `SMul Gal(E₂/K) E₂ˣ` for the intermediate field `E₂` is slow to synthesize.
/-- **Hilbert 90** for a (possibly infinite) Galois extension `Ω/K`: a 1-cocycle
`c : Gal(Ω/K) → Ωˣ` which is trivial on `Gal(Ω/E)` for some finite subextension `E/K` is a
coboundary. -/
theorem isMulCoboundary₁_of_fixingSubgroup [IsGalois K Ω] {c : Gal(Ω/K) → Ωˣ}
    (hc : IsMulCocycle₁ c) (E : IntermediateField K Ω) [FiniteDimensional K E]
    (hE : ∀ σ ∈ E.fixingSubgroup, c σ = 1) : IsMulCoboundary₁ c := by
  classical
  -- Step 1: the values of `c` form a finite set.
  set E₁ := normalClosure K E Ω
  have hsurj₁ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E₁) (E := Ω)
  have hfin : (Set.range fun σ => (c σ : Ω)).Finite := by
    refine (Set.finite_range fun τ : Gal(E₁/K) =>
      (c (Function.surjInv hsurj₁ τ) : Ω)).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨AlgEquiv.restrictNormalHom E₁ σ, ?_⟩
    simp only
    rw [eq_of_restrictNormalHom_eq hc (le_normalClosure E) hE
      (Function.surjInv_eq hsurj₁ _)]
  -- Step 2: a finite Galois subextension `E₂` containing `E` and all values of `c`.
  set S := Set.range fun σ => (c σ : Ω)
  have : Finite S := hfin.to_subtype
  have : FiniteDimensional K (adjoin K S) :=
    finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral (R := K) x)
  set F := E ⊔ adjoin K S
  set E₂ := normalClosure K F Ω
  have hEE₂ : E ≤ E₂ := le_sup_left.trans (le_normalClosure F)
  have hmem : ∀ σ, (c σ : Ω) ∈ E₂ := fun σ =>
    le_normalClosure F (le_sup_right (a := E) (subset_adjoin K S ⟨σ, rfl⟩))
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E₂) (E := Ω)
  set lift := Function.surjInv hsurj
  have hres : ∀ τ, AlgEquiv.restrictNormalHom E₂ (lift τ) = τ := Function.surjInv_eq hsurj
  have hdep : ∀ σ τ, AlgEquiv.restrictNormalHom E₂ σ = AlgEquiv.restrictNormalHom E₂ τ →
      c σ = c τ := fun σ τ h => eq_of_restrictNormalHom_eq hc hEE₂ hE h
  have happ : ∀ (σ : Gal(Ω/K)) (x : E₂),
      ((AlgEquiv.restrictNormalHom E₂ σ x : E₂) : Ω) = σ x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply E₂ σ x
  -- Step 3: descend `c` to a cocycle of the finite Galois group `Gal(E₂/K)`.
  let c₂ : Gal(E₂/K) → E₂ˣ := fun τ =>
    Units.mk0 ⟨c (lift τ), hmem _⟩ (by simp [Subtype.ext_iff])
  have hc₂val : ∀ τ, ((c₂ τ : E₂) : Ω) = c (lift τ) := fun _ => rfl
  have hc₂ : IsMulCocycle₁ c₂ := by
    intro τ₁ τ₂
    apply Units.ext
    apply Subtype.ext
    have key : c (lift (τ₁ * τ₂)) = c (lift τ₁ * lift τ₂) :=
      hdep _ _ (by rw [map_mul, hres, hres, hres])
    simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      MulMemClass.coe_mul, hc₂val]
    rw [← hres τ₁, happ, hres, hc₂val, key, hc (lift τ₁) (lift τ₂), Units.val_mul,
      AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
  -- Step 4: apply finite Hilbert 90 and lift the result back to `Ω`.
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units c₂ hc₂
  refine ⟨Units.map (algebraMap E₂ Ω : E₂ →* Ω) β, fun σ => ?_⟩
  have h1 := congrArg (fun u : E₂ˣ => ((u : E₂) : Ω)) (hβ (AlgEquiv.restrictNormalHom E₂ σ))
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map,
    MonoidHom.coe_coe, IntermediateField.coe_div, hc₂val] at h1
  rw [happ, hdep _ σ (hres _)] at h1
  apply Units.ext
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map,
    MonoidHom.coe_coe, ← h1]
  rfl

open scoped Topology in
/-- **Hilbert 90** for continuous cocycles: if `c : Gal(Ω/K) → Ωˣ` is a 1-cocycle which is
identically `1` near `1` in the Krull topology (equivalently, `c` is continuous for the discrete
topology on `Ωˣ`), then `c` is a coboundary. -/
theorem isMulCoboundary₁_of_eventually_eq_one [IsGalois K Ω] {c : Gal(Ω/K) → Ωˣ}
    (hc : IsMulCocycle₁ c) (h1 : {σ | c σ = 1} ∈ 𝓝 1) : IsMulCoboundary₁ c := by
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 h1
  exact isMulCoboundary₁_of_fixingSubgroup hc E fun σ hσ => hsub hσ

end KummerTheory
