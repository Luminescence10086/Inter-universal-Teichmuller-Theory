/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Basic
import ContinuousKummerTheory.Hilbert90

/-!
# Continuous Kummer theory

Let `Ω/K` be a (possibly infinite) Galois extension, `n` a natural number, and assume that every
`a ∈ Kˣ` has an `n`-th root in `Ω` (`KummerTheory.HasKummerRoots n K Ω`). This holds for instance
when `Ω` is separably closed and `n` is invertible in `K`.

For `a ∈ Kˣ` with `n`-th root `α ∈ Ωˣ`, the function `σ ↦ σ α / α` is a continuous
1-cocycle of `Gal(Ω/K)` with values in the discrete module `μ_n(Ω)`; its class is independent of
the choice of `α`. This gives the **Kummer map**
`κ : Kˣ →* H¹_cont(Gal(Ω/K), μ_n(Ω))`, and we prove that it induces an isomorphism

`Kˣ/(Kˣ)ⁿ ≃* H¹_cont(Gal(Ω/K), μ_n(Ω))`.

Injectivity uses that the fixed field of `Gal(Ω/K)` is `K`; surjectivity uses Hilbert 90 for
continuous cocycles (`KummerTheory.isMulCoboundary₁_of_eventually_eq_one`).

## Main definitions

* `KummerTheory.Mu n Ω` : `μ_n(Ω)`, as a discrete topological group with Galois action.
* `KummerTheory.kummerCocycle` : the cocycle `σ ↦ σ α / α`.
* `KummerTheory.kummer n K Ω : Kˣ →* ContH1 Gal(Ω/K) (Mu n Ω)` : the Kummer map.
* `KummerTheory.kummerEquiv n K Ω : Kˣ ⧸ (powMonoidHom n).range ≃* ContH1 Gal(Ω/K) (Mu n Ω)`.

## Main results

* `KummerTheory.ker_kummer` : the kernel of the Kummer map is `(Kˣ)ⁿ`.
* `KummerTheory.kummer_surjective` : the Kummer map is surjective.
-/

open groupCohomology

namespace KummerTheory

section Mu

variable (n : ℕ) (Ω : Type*) [Field Ω]

/-- The group `μ_n(Ω)` of `n`-th roots of unity of `Ω`, as a discrete topological group (with
the action of any group acting on `Ω` by ring automorphisms). -/
def Mu : Type _ := rootsOfUnity n Ω

namespace Mu

instance : CommGroup (Mu n Ω) := inferInstanceAs (CommGroup (rootsOfUnity n Ω))

instance : TopologicalSpace (Mu n Ω) := ⊥

instance : DiscreteTopology (Mu n Ω) := ⟨rfl⟩

instance : IsTopologicalGroup (Mu n Ω) where

instance [NeZero n] : Finite (Mu n Ω) := inferInstanceAs (Finite (rootsOfUnity n Ω))

variable {n Ω}

/-- The inclusion `μ_n(Ω) → Ωˣ`. -/
def val : Mu n Ω →* Ωˣ := (rootsOfUnity n Ω).subtype

theorem val_injective : Function.Injective (val : Mu n Ω → Ωˣ) := Subtype.val_injective

@[ext]
theorem ext {ζ η : Mu n Ω} (h : val ζ = val η) : ζ = η := val_injective h

/-- Build an element of `μ_n(Ω)` from a unit `ζ` with `ζ ^ n = 1`. -/
def mk (ζ : Ωˣ) (h : ζ ^ n = 1) : Mu n Ω := ⟨ζ, (mem_rootsOfUnity n ζ).2 h⟩

@[simp]
theorem val_mk (ζ : Ωˣ) (h : ζ ^ n = 1) : val (mk ζ h) = ζ := rfl

theorem val_pow_n (ζ : Mu n Ω) : val ζ ^ n = 1 := (mem_rootsOfUnity n _).1 ζ.2

@[simp]
theorem mk_val (ζ : Mu n Ω) (h : val ζ ^ n = 1) : mk (val ζ) h = ζ := rfl

variable {K : Type*} [Field K] [Algebra K Ω]

instance : MulDistribMulAction Gal(Ω/K) (Mu n Ω) where
  smul g ζ := mk (g • val ζ) (by rw [← smul_pow', val_pow_n, smul_one])
  one_smul ζ := ext (one_smul Gal(Ω/K) (val ζ))
  mul_smul g h ζ := ext (mul_smul g h (val ζ))
  smul_mul g ζ η := ext (smul_mul' g (val ζ) (val η))
  smul_one g := ext (smul_one g)

@[simp]
theorem val_smul (g : Gal(Ω/K)) (ζ : Mu n Ω) : val (g • ζ) = g • val ζ := rfl

theorem val_smul_coe (g : Gal(Ω/K)) (ζ : Mu n Ω) : ((val (g • ζ) : Ωˣ) : Ω) = g (val ζ : Ω) :=
  rfl

end Mu

end Mu

variable {n : ℕ} {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

section Cocycle

/-- The Kummer cocycle `σ ↦ σ α / α` attached to `α ∈ Ωˣ` whose `n`-th power is fixed by
`Gal(Ω/K)`. -/
def kummerFun (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) : Gal(Ω/K) → Mu n Ω :=
  fun σ => Mu.mk (σ • α / α) (by rw [div_pow, ← smul_pow', hα, div_self'])

@[simp]
theorem val_kummerFun (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) (σ : Gal(Ω/K)) :
    Mu.val (kummerFun α hα σ) = σ • α / α := rfl

theorem isMulCocycle₁_kummerFun (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) :
    IsMulCocycle₁ (kummerFun α hα) := by
  intro σ τ
  apply Mu.ext
  simp only [val_kummerFun, map_mul, Mu.val_smul, smul_div', mul_smul]
  rw [div_mul_div_cancel]

theorem continuous_kummerFun [Algebra.IsIntegral K Ω] (α : Ωˣ)
    (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) : Continuous (kummerFun α hα) := by
  refine continuous_of_mul_right_invariant (MulAction.stabilizer Gal(Ω/K) (α : Ω))
    (stabilizer_isOpen_of_isIntegral (α : Ω)) _ fun σ ν hν => ?_
  apply Mu.ext
  have hν' : ν • α = α := Units.ext hν
  simp only [val_kummerFun, mul_smul, hν']

variable [Algebra.IsIntegral K Ω]

/-- The Kummer cocycle as a continuous cocycle. -/
def kummerCocycle (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) :
    ContH1.cocycles Gal(Ω/K) (Mu n Ω) :=
  ContH1.mkCocycle (kummerFun α hα) (continuous_kummerFun α hα) (isMulCocycle₁_kummerFun α hα)

@[simp]
theorem kummerCocycle_apply (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n) (σ : Gal(Ω/K)) :
    kummerCocycle α hα σ = kummerFun α hα σ := rfl

theorem kummerCocycle_mul (α β : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n)
    (hβ : ∀ σ : Gal(Ω/K), σ • β ^ n = β ^ n) (hαβ : ∀ σ : Gal(Ω/K), σ • (α * β) ^ n = (α * β) ^ n) :
    kummerCocycle (α * β) hαβ = kummerCocycle α hα * kummerCocycle β hβ := by
  apply Subtype.ext
  funext σ
  apply Mu.ext
  change σ • (α * β) / (α * β) = (σ • α / α) * (σ • β / β)
  rw [smul_mul', mul_div_mul_comm]

theorem kummerCocycle_eq_one (α : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n)
    (hfix : ∀ σ : Gal(Ω/K), σ • α = α) : kummerCocycle α hα = 1 := by
  apply Subtype.ext
  funext σ
  apply Mu.ext
  change σ • α / α = 1
  rw [hfix, div_self']

/-- The class of the Kummer cocycle only depends on `α ^ n`. -/
theorem mk_kummerCocycle_eq (α β : Ωˣ) (hα : ∀ σ : Gal(Ω/K), σ • α ^ n = α ^ n)
    (hβ : ∀ σ : Gal(Ω/K), σ • β ^ n = β ^ n) (h : α ^ n = β ^ n) :
    ContH1.mk (kummerCocycle α hα) = ContH1.mk (kummerCocycle β hβ) := by
  rw [ContH1.mk_eq_mk_iff]
  refine ⟨Mu.mk (α / β) (by rw [div_pow, h, div_self']), fun σ => ?_⟩
  apply Mu.ext
  simp only [Mu.val_smul, Mu.val_mk, map_div, kummerCocycle_apply, val_kummerFun, smul_div']
  rw [div_div_div_comm]

end Cocycle

section KummerMap

variable (n K Ω)

/-- Every element of `Kˣ` has an `n`-th root in `Ω`. -/
class HasKummerRoots : Prop where
  exists_pow_eq : ∀ a : Kˣ, ∃ α : Ωˣ, α ^ n = Units.map (algebraMap K Ω : K →* Ω) a

instance [IsSepClosed Ω] [NeZero (n : K)] : HasKummerRoots n K Ω where
  exists_pow_eq a := by
    have hn : (n : K) ≠ 0 := NeZero.ne _
    have : NeZero (n : Ω) := ⟨by
      rw [← map_natCast (algebraMap K Ω)]
      exact (map_ne_zero _).2 hn⟩
    obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω a) n
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn0] at hz
      exact (map_ne_zero _).2 a.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

variable [HasKummerRoots n K Ω]

/-- A chosen `n`-th root in `Ω` of an element of `Kˣ`. -/
noncomputable def kummerRoot (a : Kˣ) : Ωˣ := (HasKummerRoots.exists_pow_eq (n := n) a).choose

theorem kummerRoot_pow (a : Kˣ) :
    kummerRoot n K Ω a ^ n = Units.map (algebraMap K Ω : K →* Ω) a :=
  (HasKummerRoots.exists_pow_eq a).choose_spec

variable {n K Ω}

omit [HasKummerRoots n K Ω] in
theorem smul_pow_of_pow_eq {α : Ωˣ} {a : Kˣ} (h : α ^ n = Units.map (algebraMap K Ω : K →* Ω) a)
    (σ : Gal(Ω/K)) : σ • α ^ n = α ^ n := by
  rw [h]
  ext
  simp [AlgEquiv.smul_units_def]

variable [Algebra.IsIntegral K Ω]

variable (n K Ω) in
/-- The **Kummer map** `Kˣ → H¹_cont(Gal(Ω/K), μ_n(Ω))`, `a ↦ [σ ↦ σ(a^{1/n}) / a^{1/n}]`. -/
noncomputable def kummer : Kˣ →* ContH1 Gal(Ω/K) (Mu n Ω) where
  toFun a := ContH1.mk (kummerCocycle (kummerRoot n K Ω a)
    (smul_pow_of_pow_eq (kummerRoot_pow n K Ω a)))
  map_one' := by
    rw [mk_kummerCocycle_eq _ 1 _ (fun σ => by simp)
      (by rw [kummerRoot_pow, one_pow, map_one]),
      kummerCocycle_eq_one _ _ (fun σ => smul_one σ), map_one]
  map_mul' a b := by
    have h : (kummerRoot n K Ω a * kummerRoot n K Ω b) ^ n =
        Units.map (algebraMap K Ω : K →* Ω) (a * b) := by
      rw [mul_pow, kummerRoot_pow, kummerRoot_pow, map_mul]
    rw [← map_mul, ← kummerCocycle_mul _ _ _ _ (smul_pow_of_pow_eq h)]
    exact mk_kummerCocycle_eq _ _ _ _ (by rw [kummerRoot_pow, h])

/-- The Kummer class can be computed with any `n`-th root. -/
theorem kummer_eq (a : Kˣ) (α : Ωˣ) (h : α ^ n = Units.map (algebraMap K Ω : K →* Ω) a) :
    kummer n K Ω a = ContH1.mk (kummerCocycle α (smul_pow_of_pow_eq h)) :=
  mk_kummerCocycle_eq _ _ _ _ (by rw [kummerRoot_pow, h])

end KummerMap

end KummerTheory
