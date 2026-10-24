/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Corestriction
import ContinuousKummerTheory.Kummer.Equiv

/-!
# Corestriction and the norm

Let `Ω/K` be a Galois extension and `L` a finite intermediate extension. Then
`Gal(Ω/L) → Gal(Ω/K)` is injective with image `Gal(Ω/L)` of index `[L : K]`, and the cochain
corestriction of `ContinuousKummerTheory.ContH1.Corestriction` preserves continuity of cocycles
with values in the discrete module `μ_n(Ω)`. This gives

`KummerTheory.corestriction L n : H¹_cont(Gal(Ω/L), μ_n) →* H¹_cont(Gal(Ω/K), μ_n)`.

The main result is that corestriction corresponds to the norm under the Kummer map:

`cor (κ_L a) = κ_K (N_{L/K} a)` (`KummerTheory.corestriction_kummer`).

The key input is the formula `N_{L/K}(a) = ∏ₓ r(x)(a)` over coset representatives `r(x)` of
`Gal(Ω/K) ⧸ Gal(Ω/L)` (`KummerTheory.prod_corRep_eq_norm`), deduced from Mathlib's
`Algebra.norm_eq_prod_embeddings` via a bijection between cosets and `K`-embeddings of `L` into an
algebraic closure of `Ω`.
-/

open groupCohomology IntermediateField ContH1

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)

/-- The inclusion `Gal(Ω/L) → Gal(Ω/K)`. -/
def galIncl : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K

theorem galIncl_injective : Function.Injective (galIncl L) :=
  AlgEquiv.restrictScalarsHom_injective K

@[simp]
theorem galIncl_apply (σ : Gal(Ω/L)) (x : Ω) : galIncl L σ x = σ x := rfl

theorem range_galIncl : (galIncl L).range = L.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    exact ⟨fixingSubgroupEquiv L ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

variable [IsGalois K Ω] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
theorem index_range_galIncl : (galIncl L).range.index = Module.finrank K L := by
  rw [range_galIncl, finrank_eq_fixingSubgroup_index]

instance : (galIncl L).range.FiniteIndex :=
  ⟨by rw [index_range_galIncl]; exact Module.finrank_pos.ne'⟩

noncomputable instance : Fintype (Gal(Ω/K) ⧸ (galIncl L).range) := Fintype.ofFinite _

/-- The `K`-embedding `L → Ω̄` attached to a coset of `Gal(Ω/L)` in `Gal(Ω/K)`. -/
noncomputable def cosetEmbedding (x : Gal(Ω/K) ⧸ (galIncl L).range) :
    L →ₐ[K] AlgebraicClosure Ω :=
  (IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)).comp
    ((corRep (galIncl L) x).toAlgHom.comp L.val)

theorem cosetEmbedding_bijective : Function.Bijective (cosetEmbedding L) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun x y h => ?_, ?_⟩
  · rw [← mk_corRep (galIncl L) x, ← mk_corRep (galIncl L) y, QuotientGroup.eq, range_galIncl,
      IntermediateField.mem_fixingSubgroup_iff]
    intro a ha
    have h' := congrArg (fun f : L →ₐ[K] AlgebraicClosure Ω => f ⟨a, ha⟩) h
    simp only [cosetEmbedding, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', val_mk] at h'
    have h'' : (corRep (galIncl L) x) a = (corRep (galIncl L) y) a :=
      FaithfulSMul.algebraMap_injective Ω (AlgebraicClosure Ω) h'
    rw [AlgEquiv.mul_apply, ← h'', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  · rw [Nat.card_eq_fintype_card (α := L →ₐ[K] AlgebraicClosure Ω), AlgHom.card,
      ← index_range_galIncl, Subgroup.index]

/-- The norm `N_{L/K}(a)` is the product of the conjugates `r(x)(a)` over coset representatives
of `Gal(Ω/L)` in `Gal(Ω/K)`. -/
theorem prod_corRep_eq_norm (a : L) :
    ∏ x : Gal(Ω/K) ⧸ (galIncl L).range, corRep (galIncl L) x (a : Ω) =
      algebraMap K Ω (Algebra.norm K a) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  apply FaithfulSMul.algebraMap_injective Ω (AlgebraicClosure Ω)
  rw [map_prod, ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_embeddings K _ a]
  exact Fintype.prod_bijective _ (cosetEmbedding_bijective L) _ _ fun x => rfl

/-- The corestriction of a continuous cocycle with values in `μ_n(Ω)` is continuous. -/
theorem continuous_corFun (n : ℕ) (c : cocycles Gal(Ω/L) (Mu n Ω)) :
    Continuous (corFun (galIncl L) (galIncl_injective L) (c : Gal(Ω/L) → Mu n Ω)) := by
  -- `c` is trivial on `Gal(Ω/E)` for some finite extension `E/L`
  have h1 : {σ | c σ = 1} ∈ nhds (1 : Gal(Ω/L)) := by
    have hopen : IsOpen ((c : Gal(Ω/L) → Mu n Ω) ⁻¹' {1}) :=
      (isOpen_discrete _).preimage (ContH1.continuous c)
    exact hopen.mem_nhds (by simp [ContH1.map_one_eq c])
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff L Ω _).1 h1
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.1 (E.fg_of_fg_toSubalgebra
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE)))
  -- a finite Galois extension `E'/K` containing `L` and `t`
  have : Finite t := htfin.to_subtype
  have : FiniteDimensional K (adjoin K t) :=
    finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := K) x
  set E' := normalClosure K (L ⊔ adjoin K t : IntermediateField K Ω) Ω
  have hLE' : ∀ x ∈ L, x ∈ E' := fun x hx => le_normalClosure _ (le_sup_left (b := adjoin K t) hx)
  have htE' : ∀ x ∈ t, x ∈ E' := fun x hx =>
    le_normalClosure _ (le_sup_right (a := L) (subset_adjoin K t hx))
  set N := (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E').ker
  have hmemN : ∀ ν, ν ∈ N ↔ ν ∈ E'.fixingSubgroup := fun ν => by
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    exact AlgEquiv.restrictNormal_eq_one_iff E' ν
  have hfixN : ∀ ν ∈ N, ∀ x ∈ E', ν x = x := fun ν hν =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hmemN ν).1 hν)
  have hN : N ≤ (galIncl L).range := by
    intro ν hν
    rw [range_galIncl, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hfixN ν hν x (hLE' x hx)
  have hc1 : ∀ k, galIncl L k ∈ N → c k = 1 := by
    intro k hk
    refine hsub ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hadj]
    exact (forall_mem_adjoin_smul_eq_self_iff L (S := t) k).2
      fun x hx => hfixN _ hk x (htE' x hx)
  refine continuous_of_mul_right_invariant N ?_ _ fun g ν hν =>
    corFun_mul_right (ContH1.isMulCocycle₁ c) N hN hc1 g hν
  have : (N : Set Gal(Ω/K)) = E'.fixingSubgroup := Set.ext hmemN
  rw [this]
  exact E'.fixingSubgroup_isOpen

variable (n : ℕ)

/-- The **corestriction** `H¹_cont(Gal(Ω/L), μ_n) → H¹_cont(Gal(Ω/K), μ_n)` for a finite
subextension `L/K` of a Galois extension `Ω/K`. -/
noncomputable def corestriction : ContH1 Gal(Ω/L) (Mu n Ω) →* ContH1 Gal(Ω/K) (Mu n Ω) :=
  cor (galIncl L) (galIncl_injective L) (fun _ _ => rfl) (continuous_corFun L n)

/-- **Corestriction corresponds to the norm**: `cor (κ_L a) = κ_K (N_{L/K} a)`. -/
theorem corestriction_kummer [HasKummerRoots n K Ω] [HasKummerRoots n L Ω] (a : Lˣ) :
    corestriction L n (kummer n L Ω a) =
      kummer n K Ω (Units.map (Algebra.norm K : L →* K) a) := by
  set α := kummerRoot n L Ω a
  have hα := kummerRoot_pow n L Ω a
  set β : Ωˣ := corNorm (galIncl L) α
  have hβ : β ^ n =
      Units.map (algebraMap K Ω : K →* Ω) (Units.map (Algebra.norm K : L →* K) a) := by
    ext
    simp only [β, corNorm, ← Finset.prod_pow, ← smul_pow']
    rw [hα, Units.coe_prod]
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
    exact prod_corRep_eq_norm L (a : L)
  rw [kummer_eq a α hα, kummer_eq _ β hβ, corestriction]
  erw [cor_mk]
  congr 1
  apply Subtype.ext
  funext g
  apply Mu.ext
  have h1 := congrFun (corFun_map (φ := galIncl L) (hφ := galIncl_injective L) Mu.val
    (fun _ _ => rfl) (kummerCocycle α (smul_pow_of_pow_eq hα) : Gal(Ω/L) → Mu n Ω)) g
  simp only [kummerCocycle_apply, val_kummerFun] at h1
  erw [corCocycles_apply]
  rw [← h1, corFun_coboundary (M := Ωˣ) (fun _ _ => rfl)]
  rfl

end KummerTheory
