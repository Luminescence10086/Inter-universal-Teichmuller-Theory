/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Basic

/-!
# The Kummer isomorphism `Kˣ/(Kˣ)ⁿ ≃ H¹_cont(G_K, μ_n)`

For a Galois extension `Ω/K` in which every element of `K` has an `n`-th root, the Kummer map
`KummerTheory.kummer n K Ω : Kˣ →* ContH1 Gal(Ω/K) (Mu n Ω)` has kernel `(Kˣ)ⁿ` and is
surjective, hence induces

`KummerTheory.kummerEquiv n K Ω : Kˣ ⧸ (powMonoidHom n).range ≃* ContH1 Gal(Ω/K) (Mu n Ω)`.

The main special case is `Ω` a separable closure of `K` and `n` invertible in `K`
(`KummerTheory.kummerEquivSepClosure`).
-/

open groupCohomology

namespace KummerTheory

variable (n : ℕ) (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [HasKummerRoots n K Ω]

variable {n K Ω} in
/-- An element of `Ωˣ` fixed by `Gal(Ω/K)` comes from `Kˣ`. -/
theorem exists_units_eq_of_fixed (β : Ωˣ) (h : ∀ σ : Gal(Ω/K), σ • β = β) :
    ∃ b : Kˣ, Units.map (algebraMap K Ω : K →* Ω) b = β := by
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β : Ω)).2
    fun σ => congrArg Units.val (h σ)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hb
    exact β.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩

theorem ker_kummer : (kummer n K Ω).ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro ha
    set α := kummerRoot n K Ω a
    rw [kummer_eq a α (kummerRoot_pow n K Ω a), ContH1.mk_eq_one_iff] at ha
    obtain ⟨ζ, hζ⟩ := ha
    have hfix : ∀ σ : Gal(Ω/K), σ • (α / Mu.val ζ) = α / Mu.val ζ := by
      intro σ
      have := congrArg Mu.val (hζ σ)
      simp only [map_div, Mu.val_smul, kummerCocycle_apply, val_kummerFun] at this
      rw [smul_div', div_eq_div_iff_div_eq_div, ← this]
    obtain ⟨b, hb⟩ := exists_units_eq_of_fixed _ hfix
    refine ⟨b, Units.map_injective (f := (algebraMap K Ω : K →* Ω))
      (algebraMap K Ω).injective ?_⟩
    rw [powMonoidHom_apply, map_pow, hb, div_pow, Mu.val_pow_n, div_one, kummerRoot_pow]
  · rintro ⟨b, rfl⟩
    rw [kummer_eq _ (Units.map (algebraMap K Ω : K →* Ω) b) (by simp)]
    rw [kummerCocycle_eq_one _ _ fun σ => by ext; simp [AlgEquiv.smul_units_def], map_one]

theorem kummer_surjective : Function.Surjective (kummer n K Ω) := by
  intro x
  induction x using ContH1.induction_on with
  | h c =>
  -- the cocycle `c`, viewed in `Ωˣ`, is a coboundary by Hilbert 90
  set c' : Gal(Ω/K) → Ωˣ := fun σ => Mu.val (c σ)
  have hc' : IsMulCocycle₁ c' := fun σ τ => by
    simp only [c', ContH1.isMulCocycle₁ c σ τ, map_mul, Mu.val_smul]
  have h1 : {σ | c' σ = 1} ∈ nhds (1 : Gal(Ω/K)) := by
    have hopen : IsOpen ((c : Gal(Ω/K) → Mu n Ω) ⁻¹' {1}) :=
      (isOpen_discrete _).preimage (ContH1.continuous c)
    refine Filter.mem_of_superset (hopen.mem_nhds (by simp [ContH1.map_one_eq c])) ?_
    intro σ hσ
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hσ
    simp [c', hσ]
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_eventually_eq_one hc' h1
  -- `β ^ n` is fixed, hence comes from `K`
  have hfix : ∀ σ : Gal(Ω/K), σ • β ^ n = β ^ n := by
    intro σ
    have : σ • β = c' σ * β := by rw [← hβ σ, div_mul_cancel]
    rw [smul_pow', this, mul_pow, Mu.val_pow_n, one_mul]
  obtain ⟨a, ha⟩ := exists_units_eq_of_fixed _ hfix
  refine ⟨a, ?_⟩
  rw [kummer_eq a β ha.symm]
  congr 1
  apply Subtype.ext
  funext σ
  apply Mu.ext
  simp only [kummerCocycle_apply, val_kummerFun]
  exact hβ σ

/-- **Kummer theory**: for a Galois extension `Ω/K` such that every element of `K` has an `n`-th
root in `Ω`, the Kummer map induces an isomorphism `Kˣ/(Kˣ)ⁿ ≃ H¹_cont(Gal(Ω/K), μ_n(Ω))`. -/
noncomputable def kummerEquiv :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* ContH1 Gal(Ω/K) (Mu n Ω) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_kummer n K Ω).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (kummer_surjective n K Ω))

@[simp]
theorem kummerEquiv_mk (a : Kˣ) :
    kummerEquiv n K Ω (QuotientGroup.mk a) = kummer n K Ω a := rfl

/-- **Kummer theory** for a separable closure: if `n` is invertible in `K` and `Ω` is a separable
closure of `K`, then `Kˣ/(Kˣ)ⁿ ≃ H¹_cont(Gal(Ω/K), μ_n(Ω))`. -/
noncomputable def kummerEquivSepClosure (n : ℕ) (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [NeZero (n : K)] :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* ContH1 Gal(Ω/K) (Mu n Ω) :=
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  kummerEquiv n K Ω

/-- **Kummer theory** for a perfect field and its algebraic closure: if `K` is perfect and `n` is
invertible in `K`, then `Kˣ/(Kˣ)ⁿ ≃ H¹_cont(Gal(K̄/K), μ_n(K̄))`, where `Gal(K̄/K)` is the absolute
Galois group `Field.absoluteGaloisGroup K` (definitionally `Gal(AlgebraicClosure K/K)`). -/
noncomputable def kummerEquivAlgClosure (n : ℕ) (K : Type*) [Field K] [PerfectField K]
    [NeZero (n : K)] :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃*
      ContH1 Gal(AlgebraicClosure K/K) (Mu n (AlgebraicClosure K)) :=
  kummerEquiv n K (AlgebraicClosure K)

end KummerTheory
