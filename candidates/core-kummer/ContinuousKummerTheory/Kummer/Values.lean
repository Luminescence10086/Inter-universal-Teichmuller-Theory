/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Restriction
import ContinuousKummerTheory.Kummer.Corestriction

/-!
# Kummer classes of values of functions

For the étale theta construction one needs the Kummer classes of *values* of functions at
points. We model a "function regular and invertible at a point" algebraically: `R` is a
`K`-algebra (e.g. the local ring of a curve `X/K` at a point, or the coordinate ring of an affine
open), `f ∈ Rˣ`, and a point with values in a field `L/K` is a `K`-algebra map `x : R →ₐ[K] L`
(e.g. evaluation at `x ∈ X(L)`). The value `f(x) = x f ∈ Lˣ` has a Kummer class
`κ_L(f(x)) ∈ H¹_cont(Gal(Ω_L/L), μ_n)` (`KummerTheory.kummerValue`).

We record the basic naturality properties:

* multiplicativity in `f` and vanishing on `n`-th powers;
* naturality in `R` (`KummerTheory.kummerValue_comp`) and constants
  (`KummerTheory.kummerValue_algebraMap`);
* compatibility with restriction to a bigger field of definition of the point
  (`KummerTheory.restriction_kummerValue`): the class of `f(x)` for a `K`-rational point `x`,
  restricted to `G_L`, is the class of `f(x)` with `x` viewed as an `L`-point;
* compatibility with corestriction (`KummerTheory.corestriction_kummerValue`): for a point
  defined over a finite extension `L/K` inside `Ω`, the corestriction of the class of `f(x)` is the
  class of the norm `N_{L/K}(f(x))`.

The comparison with the Kummer class of `f` itself in the cohomology of the function field, via
a decomposition group or a section attached to a rational point, is in
`ContinuousKummerTheory.Kummer.Specialization` and `ContinuousKummerTheory.Kummer.Decomposition`.
-/

namespace KummerTheory

variable (n : ℕ) {K R : Type*} [Field K] [CommRing R] [Algebra K R]

section Def

variable (L Ω : Type*) [Field L] [Algebra K L] [Field Ω] [Algebra L Ω] [Algebra.IsIntegral L Ω]
  [HasKummerRoots n L Ω]

/-- The Kummer class `κ_L(f(x)) ∈ H¹_cont(Gal(Ω/L), μ_n)` of the value at the `L`-point
`x : R →ₐ[K] L` of a function `f ∈ Rˣ`. -/
noncomputable def kummerValue (x : R →ₐ[K] L) : Rˣ →* ContH1 Gal(Ω/L) (Mu n Ω) :=
  (kummer n L Ω).comp (Units.map (x : R →* L))

variable {L Ω}

@[simp]
theorem kummerValue_apply (x : R →ₐ[K] L) (f : Rˣ) :
    kummerValue n L Ω x f = kummer n L Ω (Units.map (x : R →* L) f) := rfl

/-- Naturality in the ring of functions. -/
theorem kummerValue_comp {R' : Type*} [CommRing R'] [Algebra K R'] (φ : R →ₐ[K] R')
    (x : R' →ₐ[K] L) (f : Rˣ) :
    kummerValue n L Ω (x.comp φ) f = kummerValue n L Ω x (Units.map (φ : R →* R') f) := rfl

/-- The class of the value of a constant function. -/
theorem kummerValue_algebraMap (x : R →ₐ[K] L) (a : Kˣ) :
    kummerValue n L Ω x (Units.map (algebraMap K R : K →* R) a) =
      kummer n L Ω (Units.map (algebraMap K L : K →* L) a) := by
  simp only [kummerValue_apply]
  congr 1
  ext
  simp

/-- The class of the value of an `n`-th power vanishes. -/
theorem kummerValue_pow [IsGalois L Ω] (x : R →ₐ[K] L) (f : Rˣ) :
    kummerValue n L Ω x (f ^ n) = 1 := by
  rw [kummerValue_apply, map_pow, ← MonoidHom.mem_ker, ker_kummer]
  exact ⟨_, rfl⟩

end Def

section Restriction

variable {L ΩK ΩL : Type*} [Field L] [Field ΩK] [Field ΩL]
  [Algebra K L] [Algebra K ΩK] [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL]
  [Algebra ΩK ΩL] [IsScalarTower K ΩK ΩL] [Normal K ΩK] [Algebra.IsIntegral L ΩL]
  [Algebra.IsIntegral K ΩK] [HasKummerRoots n K ΩK] [HasKummerRoots n L ΩL]

/-- The restriction to `G_L` of the class of `f(x)` for a `K`-rational point `x` is the class of
`f(x)` with `x` regarded as an `L`-point. -/
theorem restriction_kummerValue (x : R →ₐ[K] K) (f : Rˣ) :
    restriction K L ΩK ΩL n (kummerValue n K ΩK x f) =
      kummerValue n L ΩL ((Algebra.ofId K L).comp x) f := by
  rw [kummerValue_apply, restriction_kummer, kummerValue_apply]
  congr 1

end Restriction

section Corestriction

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω] (L : IntermediateField K Ω)
  [FiniteDimensional K L] [HasKummerRoots n K Ω] [HasKummerRoots n L Ω]

/-- For a point `x` defined over a finite extension `L/K` inside `Ω`, the corestriction of the
class of `f(x)` is the class of the norm `N_{L/K}(f(x))`. -/
theorem corestriction_kummerValue (x : R →ₐ[K] L) (f : Rˣ) :
    corestriction L n (kummerValue n L Ω x f) =
      kummer n K Ω (Units.map (Algebra.norm K : L →* K) (Units.map (x : R →* L) f)) :=
  corestriction_kummer L n _

end Corestriction

end KummerTheory
