/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Values

/-!
# Kummer classes of functions versus Kummer classes of their values

Let `F` be a field (e.g. the function field of a curve over `K`, or the fraction field of a local
ring at a `K`-rational point `x`), `Ω` a Galois closure of `F` containing `n`-th roots, and `Ω_K`
one for `K`. The relation between the Kummer class `κ_F(f) ∈ H¹(Gal(Ω/F), μ_n)` of a function
`f` and the Kummer class `κ_K(f(x)) ∈ H¹(G_K, μ_n)` of its value is mediated by a
*decomposition group*: a valuation ring `B ⊆ Ω` above `x`, its stabiliser `D ⊆ Gal(Ω/F)`, the
reduction map `ψ : B → Ω_K` and the induced homomorphism `π : D → G_K`. We formalise the
statement in the following abstract form, which needs no theory of decomposition groups:

* `ι : D →* Gal(Ω/F)` and `π : D →* Gal(Ω_K/K)` are continuous homomorphisms from a topological
  group `D` (e.g. a decomposition group and its reduction map);
* `B ⊆ Ω` is a subring closed under `n`-th roots (e.g. a valuation subring,
  `KummerTheory.ValuationSubring.mem_of_pow_mem`) and stable under `ι(D)`;
* `ψ : B →+* Ω_K` is `D`-equivariant: `ψ (ι d b) = π d (ψ b)`.

Then `KummerTheory.specMu n B hB ψ : μ_n(Ω) → μ_n(Ω_K)` is the specialisation of roots of unity,
and:

* `KummerTheory.map_kummer_eq_map_kummer`: if `f ∈ Fˣ` is a unit of `B` with `ψ(f) = a ∈ Kˣ`,
  then `ι^* κ_F(f) = π^* κ_K(a)` in `H¹_cont(D, μ_n(Ω_K))` (coefficients of the left side
  specialised by `ψ`).
* `KummerTheory.map_section_kummer`: for a continuous section `s : G_K → D` of `π` (the section
  `s_x` attached to a rational point), `s^* ι^* κ_F(f) = κ_K(a)`.
* `KummerTheory.map_kummer_eq_map_kummerValue`, `KummerTheory.map_section_kummer_eq_kummerValue`:
  the same for `f ∈ Rˣ` of a `K`-algebra `R → F` and a point `x : R →ₐ[K] K` with `ψ` extending
  `x`, in terms of `KummerTheory.kummerValue n K Ω_K x f = κ_K(f(x))`.

In words: *the Kummer class of `f`, restricted along the section attached to `x`, is the Kummer
class of `f(x)`.* The general functoriality lemmas `ContH1.map_map` and `ContH1.map_id` are also
proved here.
-/

open groupCohomology

namespace ContH1

variable {G H L M N P : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group L] [TopologicalSpace L]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]
  [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [MulDistribMulAction H N]
  [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [MulDistribMulAction L P]

/-- Functoriality of `ContH1.map` with respect to composition. -/
theorem map_map (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) (ψ : L →* H) (hψ : Continuous ψ) (g : N →* P)
    (hg : Continuous g) (hcomp' : ∀ l n, g (ψ l • n) = l • g n) (x : ContH1 G M) :
    map ψ hψ g hg hcomp' (map φ hφ f hf hcomp x) =
      map (φ.comp ψ) (hφ.comp hψ) (g.comp f) (hg.comp hf)
        (fun l m => by simp [hcomp, hcomp']) x := by
  induction x using induction_on with
  | h c => rfl

/-- `ContH1.map` along the identities is the identity. -/
theorem map_id (x : ContH1 G M) :
    map (MonoidHom.id G) continuous_id (MonoidHom.id M) continuous_id (fun _ _ => rfl) x = x := by
  induction x using induction_on with
  | h c => rfl

end ContH1

namespace KummerTheory

open ContH1

variable (n : ℕ) {Ω Ω' : Type*} [Field Ω] [Field Ω'] (B : Subring Ω)
  (hB : ∀ β : Ω, β ^ n ∈ B → β ∈ B) (ψ : B →+* Ω')

/-- A unit of `Ω` with `β, β⁻¹ ∈ B` as a unit of `B`. -/
def unitOfMem (β : Ωˣ) (h₁ : (β : Ω) ∈ B) (h₂ : ((β⁻¹ : Ωˣ) : Ω) ∈ B) : Bˣ where
  val := ⟨β, h₁⟩
  inv := ⟨(β⁻¹ : Ωˣ), h₂⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

@[simp]
theorem coe_unitOfMem (β : Ωˣ) (h₁ : (β : Ω) ∈ B) (h₂ : ((β⁻¹ : Ωˣ) : Ω) ∈ B) :
    ((unitOfMem B β h₁ h₂ : Bˣ) : Ω) = β := rfl

include hB in
theorem val_mu_mem (ζ : Mu n Ω) : ((Mu.val ζ : Ωˣ) : Ω) ∈ B :=
  hB _ (by rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n]; exact B.one_mem)

include hB in
theorem val_mu_inv_mem (ζ : Mu n Ω) : (((Mu.val ζ)⁻¹ : Ωˣ) : Ω) ∈ B :=
  hB _ (by rw [← Units.val_pow_eq_pow_val, inv_pow, Mu.val_pow_n, inv_one]; exact B.one_mem)

/-- The inclusion `μ_n(Ω) → Bˣ` for a subring `B ⊆ Ω` closed under `n`-th roots. -/
def muToUnits : Mu n Ω →* Bˣ where
  toFun ζ := unitOfMem B (Mu.val ζ) (val_mu_mem n B hB ζ) (val_mu_inv_mem n B hB ζ)
  map_one' := Units.ext (Subtype.ext (by simp [unitOfMem, map_one (Mu.val (n := n) (Ω := Ω))]))
  map_mul' ζ η := Units.ext (Subtype.ext (by simp [unitOfMem]))

@[simp]
theorem coe_muToUnits (ζ : Mu n Ω) :
    ((muToUnits n B hB ζ : Bˣ) : Ω) = ((Mu.val ζ : Ωˣ) : Ω) := rfl

/-- The specialisation `μ_n(Ω) → μ_n(Ω')` of roots of unity along a ring homomorphism
`ψ : B → Ω'` defined on a subring `B ⊆ Ω` closed under `n`-th roots. -/
def specMu : Mu n Ω →* Mu n Ω' where
  toFun ζ := Mu.mk (Units.map (ψ : B →* Ω') (muToUnits n B hB ζ))
    (by
      rw [← map_pow, ← map_pow, show ζ ^ n = 1 from Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one]),
        map_one, map_one])
  map_one' := Mu.ext (by simp [Mu.val_mk])
  map_mul' ζ η := Mu.ext (by simp [Mu.val_mk])

theorem coe_val_specMu (ζ : Mu n Ω) :
    ((Mu.val (specMu n B hB ψ ζ) : Ω'ˣ) : Ω') = ψ ⟨_, val_mu_mem n B hB ζ⟩ := rfl

section Main

variable {F K Ω ΩK : Type*} [Field F] [Field K] [Field Ω] [Field ΩK] [Algebra F Ω]
  [Algebra K ΩK] {D : Type*} [Group D] [MulDistribMulAction D (Mu n ΩK)]
  (ι : D →* Gal(Ω/F)) (π : D →* Gal(ΩK/K))
  (hDact : ∀ (d : D) (ζ : Mu n ΩK), d • ζ = π d • ζ)
  (B : Subring Ω) (hB : ∀ β : Ω, β ^ n ∈ B → β ∈ B)
  (hstab : ∀ (d : D) (b : Ω), b ∈ B → ι d b ∈ B)
  (ψ : B →+* ΩK) (hψ : ∀ (d : D) (b : B), ψ ⟨ι d b, hstab d b b.2⟩ = π d (ψ b))

include hDact hψ in
theorem specMu_smul (d : D) (ζ : Mu n Ω) :
    specMu n B hB ψ (ι d • ζ) = d • specMu n B hB ψ ζ := by
  rw [hDact]
  apply Mu.ext
  apply Units.ext
  rw [Mu.val_smul_coe, coe_val_specMu, coe_val_specMu, ← hψ]
  rfl

variable [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K ΩK] [HasKummerRoots n F Ω]
  [HasKummerRoots n K ΩK] [TopologicalSpace D] (hι : Continuous ι) (hπ : Continuous π)

/-- **Specialisation of Kummer classes.** Let `ι : D → Gal(Ω/F)` and `π : D → Gal(Ω_K/K)` be
continuous homomorphisms (e.g. the inclusion of a decomposition group and its reduction map), and
`ψ : B → Ω_K` a ring homomorphism on a `D`-stable subring `B ⊆ Ω` closed under `n`-th roots
which is `D`-equivariant (`ψ (ι d b) = π d (ψ b)`). If `f ∈ Fˣ` is a unit of `B` with
specialisation `ψ f = a ∈ Kˣ`, then the pull-back along `ι` of the Kummer class `κ_F(f)`, with
coefficients specialised by `ψ`, is the pull-back along `π` of `κ_K(a)`. -/
theorem map_kummer_eq_map_kummer (f : Fˣ) (a : Kˣ) (hf : algebraMap F Ω f ∈ B)
    (hf' : algebraMap F Ω ↑f⁻¹ ∈ B) (hfa : ψ ⟨_, hf⟩ = algebraMap K ΩK a) :
    ContH1.map ι hι (specMu n B hB ψ) continuous_of_discreteTopology
        (specMu_smul n ι π hDact B hB hstab ψ hψ) (kummer n F Ω f) =
      ContH1.map π hπ (MonoidHom.id _) continuous_id (fun d ζ => (hDact d ζ).symm)
        (kummer n K ΩK a) := by
  have hα := kummerRoot_pow n F Ω f
  set α := kummerRoot n F Ω f
  have hαB : (α : Ω) ∈ B := hB _ (by rw [← Units.val_pow_eq_pow_val, hα]; exact hf)
  have hαB' : ((α⁻¹ : Ωˣ) : Ω) ∈ B :=
    hB _ (by rw [← Units.val_pow_eq_pow_val, inv_pow, hα, ← map_inv]; exact hf')
  set β : ΩKˣ := Units.map (ψ : B →* ΩK) (unitOfMem B α hαB hαB') with hβ_def
  have hβ : β ^ n = Units.map (algebraMap K ΩK : K →* ΩK) a := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hβ_def, Units.coe_map, MonoidHom.coe_coe, ← map_pow,
      Units.coe_map, MonoidHom.coe_coe, ← hfa]
    congr 1
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, coe_unitOfMem]
    rw [← Units.val_pow_eq_pow_val, hα]
    rfl
  rw [kummer_eq f α hα, kummer_eq a β hβ, map_mk, map_mk]
  congr 1
  apply Subtype.ext
  funext d
  apply Mu.ext
  apply Units.ext
  rw [cocyclesMap_apply, cocyclesMap_apply, coe_val_specMu]
  have hmem : ι d (α : Ω) ∈ B := hstab d _ hαB
  have h1 : (⟨((Mu.val (kummerCocycle α (smul_pow_of_pow_eq hα) (ι d)) : Ωˣ) : Ω),
      val_mu_mem n B hB _⟩ : B) = ⟨ι d (α : Ω), hmem⟩ * ⟨((α⁻¹ : Ωˣ) : Ω), hαB'⟩ := by
    apply Subtype.ext
    simp [AlgEquiv.smul_units_def, div_eq_mul_inv]
  have hinv : ψ ⟨((α⁻¹ : Ωˣ) : Ω), hαB'⟩ = (ψ ⟨α, hαB⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul]
    convert map_one ψ
    apply Subtype.ext
    simp
  rw [h1, map_mul, hψ d ⟨α, hαB⟩, hinv]
  simp [hβ_def, AlgEquiv.smul_units_def, div_eq_mul_inv]
  rfl

include hDact hπ in
/-- **Kummer classes along a section.** In the situation of `map_kummer_eq_map_kummer`, if
`s : Gal(Ω_K/K) → D` is a continuous section of `π` (e.g. the section `s_x` of the arithmetic
fundamental group attached to a rational point), then pulling back `κ_F(f)` along `ι ∘ s` (with
coefficients specialised by `ψ`) gives `κ_K(a)`. -/
theorem map_section_kummer (s : Gal(ΩK/K) →* D) (hs : Continuous s) (hπs : ∀ g, π (s g) = g)
    (f : Fˣ) (a : Kˣ) (hf : algebraMap F Ω f ∈ B) (hf' : algebraMap F Ω ↑f⁻¹ ∈ B)
    (hfa : ψ ⟨_, hf⟩ = algebraMap K ΩK a) :
    ContH1.map s hs (MonoidHom.id _) continuous_id (fun g ζ => by rw [hDact, hπs]; rfl)
        (ContH1.map ι hι (specMu n B hB ψ) continuous_of_discreteTopology
          (specMu_smul n ι π hDact B hB hstab ψ hψ) (kummer n F Ω f)) =
      kummer n K ΩK a := by
  rw [map_kummer_eq_map_kummer n ι π hDact B hB hstab ψ hψ hι hπ f a hf hf' hfa, ContH1.map_map]
  induction kummer n K ΩK a using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext g
    simp [hπs]

end Main

section Values

variable {K F R Ω ΩK : Type*} [Field K] [Field F] [CommRing R] [Algebra K R] [Algebra R F]
  [Field Ω] [Field ΩK] [Algebra F Ω] [Algebra K ΩK] {D : Type*} [Group D]
  [MulDistribMulAction D (Mu n ΩK)] (ι : D →* Gal(Ω/F)) (π : D →* Gal(ΩK/K))
  (hDact : ∀ (d : D) (ζ : Mu n ΩK), d • ζ = π d • ζ)
  (B : Subring Ω) (hB : ∀ β : Ω, β ^ n ∈ B → β ∈ B)
  (hstab : ∀ (d : D) (b : Ω), b ∈ B → ι d b ∈ B)
  (ψ : B →+* ΩK) (hψ : ∀ (d : D) (b : B), ψ ⟨ι d b, hstab d b b.2⟩ = π d (ψ b))
  [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K ΩK] [HasKummerRoots n F Ω]
  [HasKummerRoots n K ΩK] [TopologicalSpace D] (hι : Continuous ι) (hπ : Continuous π)

/-- **The Kummer class of a function specialises to the Kummer class of its value.** Let `R` be
a `K`-algebra with a map to a field `F` (e.g. the local ring at a `K`-rational point `x` of a
curve, with `F` its function field), `x : R →ₐ[K] K` a point, and `ψ : B → Ω_K` a `D`-equivariant
specialisation on a subring `B ⊆ Ω` closed under `n`-th roots that extends `x` on `R`
(`hRB`, `hψx`). Then for `f ∈ Rˣ`, the class `κ_F(f)` pulled back along `ι` (coefficients
specialised by `ψ`) equals `κ_K(f(x)) = kummerValue n K ΩK x f` pulled back along `π`. -/
theorem map_kummer_eq_map_kummerValue (x : R →ₐ[K] K)
    (hRB : ∀ r : R, algebraMap F Ω (algebraMap R F r) ∈ B)
    (hψx : ∀ r : R, ψ ⟨_, hRB r⟩ = algebraMap K ΩK (x r)) (f : Rˣ) :
    ContH1.map ι hι (specMu n B hB ψ) continuous_of_discreteTopology
        (specMu_smul n ι π hDact B hB hstab ψ hψ)
        (kummer n F Ω (Units.map (algebraMap R F : R →* F) f)) =
      ContH1.map π hπ (MonoidHom.id _) continuous_id (fun d ζ => (hDact d ζ).symm)
        (kummerValue n K ΩK x f) := by
  rw [kummerValue_apply]
  refine map_kummer_eq_map_kummer n ι π hDact B hB hstab ψ hψ hι hπ _ _ (hRB f) ?_ ?_
  · simpa using hRB ↑f⁻¹
  · simpa using hψx f

include hπ in
/-- Section form of `map_kummer_eq_map_kummerValue`: along a continuous section `s` of `π`, the
Kummer class of the function `f` restricts to the Kummer class `κ_K(f(x))` of its value. -/
theorem map_section_kummer_eq_kummerValue (s : Gal(ΩK/K) →* D) (hs : Continuous s)
    (hπs : ∀ g, π (s g) = g) (x : R →ₐ[K] K)
    (hRB : ∀ r : R, algebraMap F Ω (algebraMap R F r) ∈ B)
    (hψx : ∀ r : R, ψ ⟨_, hRB r⟩ = algebraMap K ΩK (x r)) (f : Rˣ) :
    ContH1.map s hs (MonoidHom.id _) continuous_id (fun g ζ => by rw [hDact, hπs]; rfl)
        (ContH1.map ι hι (specMu n B hB ψ) continuous_of_discreteTopology
          (specMu_smul n ι π hDact B hB hstab ψ hψ)
          (kummer n F Ω (Units.map (algebraMap R F : R →* F) f))) =
      kummerValue n K ΩK x f := by
  rw [kummerValue_apply]
  refine map_section_kummer n ι π hDact B hB hstab ψ hψ hι hπ s hs hπs _ _ (hRB f) ?_ ?_
  · simpa using hRB ↑f⁻¹
  · simpa using hψx f

end Values

/-- A valuation subring is closed under `n`-th roots (`n ≠ 0`). -/
theorem ValuationSubring.mem_of_pow_mem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {n : ℕ}
    (hn : n ≠ 0) {β : Ω} (h : β ^ n ∈ A) : β ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

end KummerTheory
