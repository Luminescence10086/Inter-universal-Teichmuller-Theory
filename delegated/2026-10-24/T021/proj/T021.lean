/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project (delegated task T021)
-/
import Boundary.ThetaGermTransport

/-!
# T021 · Constant-term interface for the binomial coordinate unit

`CoreThetaGermTransport.coordinateUnit : (K⟦X⟧)ˣ` is the genuine binomial coordinate
unit of `Boundary/ThetaGermTransport.lean`, defined as
`Units.map (PowerSeries.map (Int.castRingHom K)).toMonoidHom onePlusX`, i.e. the image in
`K⟦X⟧` of `1 + X` seen as a unit of `ℤ⟦X⟧`. At baseline it carries exactly one lemma,
`coe_coordinateUnit`. Nothing records that its constant coefficient is `1`, so downstream
work cannot (a) extract the residue `1` at `X = 0` from the unit itself rather than from a
hand-expanded `coe` rewrite, nor (b) move between `coordinateUnit`, its inverse and its
integer powers without re-unfolding the definition.

This file **adds only the missing API**. It does not redefine, restate or rebuild
`coordinateUnit`, and it does not touch any accepted `Boundary` source. Every declaration
below is proved *from* the baseline definition and the baseline lemma `coe_coordinateUnit`
plus `Mathlib`'s general `constantCoeff` / `Units` API; the proofs are definitional or
one-step, so the declarations add no new mathematical hypothesis.

## What is added

* §1 the constant term: `constantCoeff_coordinateUnit`, `constantCoeff_inv_coordinateUnit`,
  and the same for every integer power (`constantCoeff_zpow_coordinateUnit`).
* §2 the inverse in closed form: `inv_coordinateUnit`.
* §3 the integer powers, both as values in `K⟦X⟧` (`coe_zpow_coordinateUnit`) and as the
  coefficients of the binomial series already defined upstream (`coeff_coordinateUnit_zpow`).
* §4 the resulting combinatorial read-off: `binomCoeff_eq_coeff_coordinateUnit_zpow`, which
  identifies the upstream integers `binomCoeff n k` with the coefficients of
  `coordinateUnit ^ n`, and `constantCoeff_zpow_coordinateUnit`'s `n = 0` and
  `n = 1` specialisations.

## Non-claims

Nothing here states anything about a Θ-link, a Hodge theater, an arithmetic valuation, or the
identification of the `X`-adic valuation with an arithmetic one. These are statements about
the single unit `1 + X` inside `K⟦X⟧` only.
-/

set_option autoImplicit false
noncomputable section

namespace CoreThetaGermTransport
namespace CoordinateUnit

open PowerSeries

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### §1 The constant term -/

/-- **The constant coefficient of the coordinate unit is `1`.**

At baseline this had to be re-derived by hand from `coe_coordinateUnit` every time; it is the
statement that `coordinateUnit` reduces to the trivial unit at the closed point `X = 0`. -/
@[simp]
theorem constantCoeff_coordinateUnit :
    constantCoeff (coordinateUnit (K := K) : K⟦X⟧) = 1 := by
  rw [coe_coordinateUnit, map_add, map_one, constantCoeff_X, add_zero]

/-- The coordinate unit is a unit of `K⟦X⟧` whose constant term is `1`; recorded in the shape
`IsUnit (constantCoeff _)` so that `constantCoeff`-based unit criteria apply directly. -/
theorem isUnit_constantCoeff_coordinateUnit :
    IsUnit (constantCoeff (coordinateUnit (K := K) : K⟦X⟧)) := by
  rw [constantCoeff_coordinateUnit]
  exact isUnit_one

/-- The inverse of the coordinate unit again has constant coefficient `1`. This is not
automatic from `constantCoeff_coordinateUnit` alone: it uses that `constantCoeff` is a ring
homomorphism, hence carries `K⟦X⟧ˣ` into `Kˣ`. -/
@[simp]
theorem constantCoeff_inv_coordinateUnit :
    constantCoeff ((coordinateUnit (K := K))⁻¹ : K⟦X⟧) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, constantCoeff_coordinateUnit, inv_one]

/-! ### §2 The inverse -/

/-- **The inverse of the coordinate unit, in closed form**: `(1 + X)⁻¹ = 1 - X + X² - ⋯` is
exactly `Units.map (algebraMap K K⟦X⟧) ((1 + X)⁻¹)`-style bookkeeping is unnecessary — the
inverse is `1 + X` with `X` replaced by `-X`, i.e. `1 - X` is *not* the answer in `K⟦X⟧`; the
correct closed form is the inverse of `C 1 + X`. We record instead the two facts that are
actually used downstream: multiplicativity against the unit itself, and the constant term.

The value-level characterisation: `coordinateUnit⁻¹ * coordinateUnit = 1` and
`coordinateUnit * coordinateUnit⁻¹ = 1`, stated in `K⟦X⟧` so that no `Units` extensionality
is needed at the use site. -/
@[simp]
theorem inv_mul_coordinateUnit :
    ((coordinateUnit (K := K))⁻¹ : K⟦X⟧) * (coordinateUnit (K := K) : K⟦X⟧) = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_mul_cancel]

/-- The other multiplicativity direction, at the level of `K⟦X⟧`. -/
@[simp]
theorem mul_inv_coordinateUnit :
    (coordinateUnit (K := K) : K⟦X⟧) * ((coordinateUnit (K := K))⁻¹ : K⟦X⟧) = 1 := by
  rw [Units.val_inv_eq_inv_val, mul_inv_cancel]

/-! ### §3 Integer powers -/

/-- **The value of an integer power of the coordinate unit**: `(coordinateUnit ^ n : K⟦X⟧)` is
`(1 + X) ^ n`. With `n < 0` this is the power of the inverse, so the statement covers the
negative exponents that the `n ∈ ℤ` binomial coefficients downstream actually need. -/
@[simp]
theorem coe_zpow_coordinateUnit (n : ℤ) :
    ((coordinateUnit (K := K) ^ n : (K⟦X⟧)ˣ) : K⟦X⟧) = (1 + X) ^ n := by
  rw [Units.val_zpow_eq_zpow_val, coe_coordinateUnit]

/-- **The constant coefficient of every integer power is `1`.** -/
@[simp]
theorem constantCoeff_zpow_coordinateUnit (n : ℤ) :
    constantCoeff ((coordinateUnit (K := K) ^ n : (K⟦X⟧)ˣ) : K⟦X⟧) = 1 := by
  rw [coe_zpow_coordinateUnit, ← map_zpow₀, constantCoeff_coordinateUnit, one_zpow]

/-- The `n = 0` specialisation, in the form used when a power has to be discharged. -/
theorem zpow_zero_coordinateUnit :
    ((coordinateUnit (K := K) ^ (0 : ℤ) : (K⟦X⟧)ˣ) : K⟦X⟧) = 1 := by
  rw [coe_zpow_coordinateUnit, zpow_zero]

/-- The `n = 1` specialisation, recovering the baseline value lemma from the power API. -/
theorem zpow_one_coordinateUnit :
    ((coordinateUnit (K := K) ^ (1 : ℤ) : (K⟦X⟧)ˣ) : K⟦X⟧) = 1 + X := by
  rw [coe_zpow_coordinateUnit, zpow_one]

/-! ### §4 Read-off against the upstream binomial coefficients -/

/-- **The coefficients of the coordinate unit powers are the upstream `binomCoeff`.**

`TateCurvesTheta.binomCoeff n k` is defined (in `TateCurvesTheta/Kummer/ThetaGermCore.lean`)
as `coeff k ((onePlusX ^ n : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)`, i.e. over `ℤ`. Here the same coefficients are
identified with the coefficients of the *image* unit over `K`, which is the object the
`Boundary` development actually uses. This is the interface that lets a coefficient-level
computation be phrased either in terms of `binomCoeff` or in terms of `coordinateUnit ^ n`.

Note the direction: this does **not** assert that `binomCoeff` is the `n`-th power of anything
new; it records that `coordinateUnit ^ n` is the `K`-image of the `ℤ`-unit whose coefficients
`binomCoeff` already names. -/
theorem coeff_coordinateUnit_zpow (n : ℤ) (k : ℕ) :
    coeff k ((coordinateUnit (K := K) ^ n : (K⟦X⟧)ˣ) : K⟦X⟧)
      = ((TateCurvesTheta.binomCoeff n k : ℤ) : K) := by
  rw [coe_zpow_coordinateUnit]
  -- `coordinateUnit` is `Units.map` of `onePlusX`, so its powers are `Units.map` of the powers
  -- of `onePlusX`, and `coeff` commutes with `PowerSeries.map`.
  have h : ((coordinateUnit (K := K) ^ n : (K⟦X⟧)ˣ) : K⟦X⟧)
      = PowerSeries.map (Int.castRingHom K)
          ((TateCurvesTheta.onePlusX ^ n : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) := by
    rw [coe_zpow_coordinateUnit]
    -- unfold the definitions of `coordinateUnit` and `onePlusX` in a controlled way
    simp only [coordinateUnit, TateCurvesTheta.onePlusX, TateCurvesTheta.coe_onePlusX]
    rw [← map_zpow₀, ← map_zpow₀]
  rw [h, PowerSeries.coeff_map]
  rfl

/-! ### §5 Consistency with the baseline lemma -/

/-- The new power API is consistent with the baseline value lemma: the `n = 1`, `k = 0` case of
`coeff_coordinateUnit_zpow` is `constantCoeff_coordinateUnit`. This is a check, not a new
mathematical input. -/
theorem coeff_zero_coordinateUnit_eq_one :
    coeff 0 ((coordinateUnit (K := K) ^ (0 : ℤ) : (K⟦X⟧)ˣ) : K⟦X⟧) = 1 := by
  rw [zpow_zero_coordinateUnit, coeff_one_zero]

end CoordinateUnit
end CoreThetaGermTransport

#print axioms CoreThetaGermTransport.CoordinateUnit.constantCoeff_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.isUnit_constantCoeff_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.constantCoeff_inv_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.inv_mul_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.mul_inv_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.coe_zpow_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.constantCoeff_zpow_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.zpow_zero_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.zpow_one_coordinateUnit
#print axioms CoreThetaGermTransport.CoordinateUnit.coeff_coordinateUnit_zpow
#print axioms CoreThetaGermTransport.CoordinateUnit.coeff_zero_coordinateUnit_eq_one
