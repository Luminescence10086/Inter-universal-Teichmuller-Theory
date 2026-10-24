/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Specialization
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Kummer classes on decomposition groups

Let `k → F → Ω` be fields with `Ω/F` algebraic (e.g. `F` a function field over the constants `k`
and `Ω` a separable closure of `F`), and let `A ⊆ Ω` be a valuation subring containing (the image
of) `k`, with residue field `κ(A)`. The decomposition group `D_A ⊆ Gal(Ω/F)` (Mathlib's
`ValuationSubring.decompositionSubgroup`) acts on `A`, hence on `κ(A)`, by `k`-automorphisms.

We construct the **decomposition map** `KummerTheory.Decomposition.decompositionMap :
D_A →* Gal(κ(A)/k)`, `σ ↦ (residue b ↦ residue (σ b))`, show that its kernel is Mathlib's inertia
subgroup (`ker_decompositionMap`) and that it is continuous for the Krull topologies
(`continuous_decompositionMap`).

We then instantiate the specialisation theorem `KummerTheory.map_kummer_eq_map_kummer` with
`ι = D_A ↪ Gal(Ω/F)`, `π = decompositionMap`, `B = A` (closed under `n`-th roots) and
`ψ = residue : A → κ(A)`:

* `decomposition_kummer`: if `f ∈ Fˣ` is a unit at `A` with residue the constant `a ∈ kˣ`, then
  the restriction of `κ_F(f)` to `D_A` (coefficients reduced mod `𝔪_A`) is the inflation along
  `decompositionMap` of `κ_k(a)`;
* `decomposition_kummerValue`: the same for `f ∈ Rˣ`, `R → F` a `k`-algebra with a point
  `x : R →ₐ[k] k` compatible with reduction, with `κ_k(f(x)) = kummerValue n k κ(A) x f`.

## Implementation notes

The `k`-algebra structure on `κ(A)` is taken as an instance argument `[Algebra k (ResidueField A)]`
together with a compatibility hypothesis `hkres` with the reduction of `algebraMap k Ω`. The
canonical choice `residueAlgebra A hk` satisfies `hkres` by `rfl`
(`residue_algebraMap_residueAlgebra`). The action of `D_A` on `μ_n(κ(A))` through
`decompositionMap` depends on these hypotheses, so it is a `def` (`muAction`) used via `letI`.
-/

open IsLocalRing

namespace KummerTheory

namespace Decomposition

variable {k : Type*} (F : Type*) {Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F]
  [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)

/-- The canonical `k`-algebra structure on the residue field of a valuation subring `A ⊆ Ω`
containing the image of `k`. -/
@[implicit_reducible]
noncomputable def residueAlgebra : Algebra k (ResidueField A) :=
  ((residue A).comp ((algebraMap k Ω).codRestrict A.toSubring hk)).toAlgebra

/-- The algebra structure `residueAlgebra` satisfies the compatibility hypothesis `hkres` used
throughout this file. -/
theorem residue_algebraMap_residueAlgebra (c : k) :
    residue A ⟨algebraMap k Ω c, hk c⟩ =
      @algebraMap k (ResidueField A) _ _ (residueAlgebra A hk) c := rfl

variable [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

include hkres in
/-- Elements of the decomposition group act trivially on the constants of `κ(A)`. -/
theorem smul_algebraMap (σ : A.decompositionSubgroup F) (c : k) :
    σ • algebraMap k (ResidueField A) c = algebraMap k (ResidueField A) c := by
  rw [← hkres, ← ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  change σ.1 (algebraMap k Ω c) = algebraMap k Ω c
  simp only [IsScalarTower.algebraMap_apply k F Ω c, AlgEquiv.commutes]

/-- The **decomposition map** `D_A → Gal(κ(A)/k)` from the decomposition group of the valuation
subring `A ⊆ Ω` to the automorphism group of its residue field over the constants `k`. -/
noncomputable def decompositionMap :
    A.decompositionSubgroup F →* Gal(ResidueField A/k) where
  toFun σ := AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ (ResidueField A) σ)
    (smul_algebraMap F A hk hkres σ)
  map_one' := AlgEquiv.ext fun x => one_smul (A.decompositionSubgroup F) x
  map_mul' σ τ := AlgEquiv.ext fun x => mul_smul σ τ x

theorem decompositionMap_apply (σ : A.decompositionSubgroup F) (x : ResidueField A) :
    decompositionMap F A hk hkres σ x = σ • x := rfl

theorem decompositionMap_residue (σ : A.decompositionSubgroup F) (b : A) :
    decompositionMap F A hk hkres σ (residue A b) = residue A (σ • b) :=
  (ResidueField.residue_smul _ _ _).symm

/-- The kernel of the decomposition map is the inertia subgroup. -/
theorem ker_decompositionMap :
    (decompositionMap F A hk hkres).ker = A.inertiaSubgroup F := by
  ext σ
  simp only [MonoidHom.mem_ker, ValuationSubring.inertiaSubgroup]
  constructor
  · intro h
    ext x
    exact DFunLike.congr_fun h x
  · intro h
    ext x
    exact DFunLike.congr_fun h x

/-- The decomposition map is continuous for the Krull topologies (the decomposition group carrying
the subspace topology). -/
theorem continuous_decompositionMap [Algebra.IsIntegral F Ω] :
    Continuous (decompositionMap F A hk hkres) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff k _ U).1 hU
  obtain ⟨t, htfin, rfl⟩ := IntermediateField.fg_def.1
    (E.fg_of_fg_toSubalgebra (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.1 hE)))
  choose lift hlift using fun x : ResidueField A => residue_surjective x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((Filter.biInter_mem htfin).2 fun x _ =>
    ((continuous_subtype_val (p := (· ∈ A.decompositionSubgroup F)).isOpen_preimage _
      (stabilizer_isOpen_of_isIntegral ((lift x : A) : Ω))).mem_nhds
        (show (1 : Gal(Ω/F)) ∈ MulAction.stabilizer _ _ from one_mem _))) ?_
  intro σ hσ
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    at hσ
  apply hEU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff k
    (decompositionMap F A hk hkres σ)).2 (fun y hy => ?_) x hx
  rw [AlgEquiv.smul_def, ← hlift y, decompositionMap_residue]
  congr 1
  exact Subtype.ext (hσ y hy)

section Kummer

variable (n : ℕ) (hn : n ≠ 0)

/-- The action of the decomposition group on `μ_n(κ(A))` through the decomposition map. -/
@[implicit_reducible]
noncomputable def muAction :
    MulDistribMulAction (A.decompositionSubgroup F) (Mu n (ResidueField A)) :=
  MulDistribMulAction.compHom _ (decompositionMap F A hk hkres)

include hn in
/-- `A` is closed under `n`-th roots (`n ≠ 0`). -/
theorem mem_of_pow_mem_toSubring (β : Ω) (h : β ^ n ∈ A.toSubring) : β ∈ A.toSubring :=
  ValuationSubring.mem_of_pow_mem A hn h

/-- The reduction map `μ_n(Ω) → μ_n(κ(A))` (note that `μ_n(Ω) ⊆ A`). -/
noncomputable def reduceMu : Mu n Ω →* Mu n (ResidueField A) :=
  specMu n A.toSubring (mem_of_pow_mem_toSubring A n hn) (residue A)

/-- `A` is stable under its decomposition group. -/
theorem smul_mem_toSubring (σ : A.decompositionSubgroup F) (b : Ω) (hb : b ∈ A.toSubring) :
    (σ : Gal(Ω/F)) b ∈ A.toSubring :=
  (σ • (⟨b, hb⟩ : A)).2

/-- Reduction modulo `𝔪_A` is equivariant along the decomposition map. -/
theorem residue_smul_eq (σ : A.decompositionSubgroup F) (b : A.toSubring) :
    residue A ⟨(σ : Gal(Ω/F)) b, smul_mem_toSubring F A σ b b.2⟩ =
      decompositionMap F A hk hkres σ (residue A b) :=
  (decompositionMap_residue F A hk hkres σ b).symm

/-- Reduction of roots of unity is equivariant along the decomposition map. -/
theorem reduceMu_smul (σ : A.decompositionSubgroup F) (ζ : Mu n Ω) :
    letI := muAction F A hk hkres n
    reduceMu A n hn ((A.decompositionSubgroup F).subtype σ • ζ) = σ • reduceMu A n hn ζ :=
  letI := muAction F A hk hkres n
  specMu_smul n (A.decompositionSubgroup F).subtype (decompositionMap F A hk hkres)
    (fun _ _ => rfl) A.toSubring _ (smul_mem_toSubring F A) (residue A)
    (residue_smul_eq F A hk hkres) σ ζ

variable [Algebra.IsIntegral F Ω] [Algebra.IsIntegral k (ResidueField A)] [HasKummerRoots n F Ω]
  [HasKummerRoots n k (ResidueField A)]

/-- **Kummer classes on the decomposition group.** Let `A ⊆ Ω` be a valuation subring containing
the constants `k`, with residue field `κ(A)`, and let `f ∈ Fˣ` be a unit at `A` (`f, f⁻¹ ∈ A`)
whose residue is the constant `a ∈ kˣ`. Then the restriction of the Kummer class `κ_F(f)` to
the decomposition group `D_A` (with coefficients reduced modulo the maximal ideal of `A`) is
the inflation along the decomposition map `D_A → Gal(κ(A)/k)` of the Kummer class `κ_k(a)`. -/
theorem decomposition_kummer (f : Fˣ) (a : kˣ) (hf : algebraMap F Ω f ∈ A)
    (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) a) :
    letI := muAction F A hk hkres n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val (reduceMu A n hn)
        continuous_of_discreteTopology (reduceMu_smul F A hk hkres n hn) (kummer n F Ω f) =
      ContH1.map (decompositionMap F A hk hkres) (continuous_decompositionMap F A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl) (kummer n k (ResidueField A) a) :=
  letI := muAction F A hk hkres n
  map_kummer_eq_map_kummer n (A.decompositionSubgroup F).subtype (decompositionMap F A hk hkres)
    (fun _ _ => rfl) A.toSubring (mem_of_pow_mem_toSubring A n hn) (smul_mem_toSubring F A)
    (residue A) (residue_smul_eq F A hk hkres) continuous_subtype_val
    (continuous_decompositionMap F A hk hkres) f a hf hf' hfa

/-- **Kummer classes of functions on the decomposition group.** Let `R` be a `k`-algebra mapping
to `F` (e.g. the local ring of a curve at a `k`-rational point, `F` its function field) whose
elements lie in `A`, and `x : R →ₐ[k] k` a point compatible with reduction modulo `A`
(`hRx`). Then for `f ∈ Rˣ` the restriction of `κ_F(f)` to the decomposition group `D_A`
is the inflation along the decomposition map of `κ_k(f(x)) = kummerValue n k κ(A) x f`. -/
theorem decomposition_kummerValue {R : Type*} [CommRing R] [Algebra k R] [Algebra R F]
    (x : R →ₐ[k] k) (hRA : ∀ r : R, algebraMap F Ω (algebraMap R F r) ∈ A)
    (hRx : ∀ r : R, residue A ⟨_, hRA r⟩ = algebraMap k (ResidueField A) (x r)) (f : Rˣ) :
    letI := muAction F A hk hkres n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val (reduceMu A n hn)
        continuous_of_discreteTopology (reduceMu_smul F A hk hkres n hn)
        (kummer n F Ω (Units.map (algebraMap R F : R →* F) f)) =
      ContH1.map (decompositionMap F A hk hkres) (continuous_decompositionMap F A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl) (kummerValue n k (ResidueField A) x f) :=
  letI := muAction F A hk hkres n
  map_kummer_eq_map_kummerValue n (A.decompositionSubgroup F).subtype
    (decompositionMap F A hk hkres) (fun _ _ => rfl) A.toSubring (mem_of_pow_mem_toSubring A n hn)
    (smul_mem_toSubring F A) (residue A) (residue_smul_eq F A hk hkres) continuous_subtype_val
    (continuous_decompositionMap F A hk hkres) x hRA hRx f

end Kummer

end Decomposition

end KummerTheory
