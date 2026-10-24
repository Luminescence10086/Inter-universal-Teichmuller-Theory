/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project

The source interface and the ratio construction are adapted from
Iut/EtaleTheta/Wall.lean, `pow_eq_thetaRatio_inv_iff`, commit
f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb (Apache 2.0).
The integral-closure stability conclusions below are a separate generic bridge.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Finite-order ambiguity preserves maximal-order principal lattices

The external theta interface writes a chosen root as `ζ * lgpValue`, with
`ζ ^ ell = 1`. A finite-order scalar is a unit of the integral closure, so this
particular root-choice ambiguity preserves every principal integral-closure set.
This does not address all Ind1/Ind2/Ind3 ambiguities or instantiate the packet.
-/
set_option autoImplicit false

namespace CoreTorsionHullStability

open scoped Pointwise

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [Field A] [Algebra R A]
  {ell : ℕ} {ζ : A}

theorem torsion_ne_zero (hell : 0 < ell) (hζ : ζ ^ ell = 1) : ζ ≠ 0 := by
  intro hz
  simp [hz, zero_pow hell.ne'] at hζ

theorem torsion_isIntegral (hell : 0 < ell) (hζ : ζ ^ ell = 1) :
    IsIntegral R ζ :=
  IsIntegral.of_pow hell (hζ.symm ▸ isIntegral_one)

theorem torsion_inv_isIntegral (hell : 0 < ell) (hζ : ζ ^ ell = 1) :
    IsIntegral R ζ⁻¹ := by
  apply torsion_isIntegral hell
  rw [inv_pow, hζ, inv_one]

/-- The finite-order scalar is an actual unit of the integral-closure ring. -/
def torsionUnit (hell : 0 < ell) (hζ : ζ ^ ell = 1) : (integralClosure R A)ˣ where
  val := ⟨ζ, torsion_isIntegral hell hζ⟩
  inv := ⟨ζ⁻¹, torsion_inv_isIntegral hell hζ⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (torsion_ne_zero hell hζ))
  inv_val := Subtype.ext (inv_mul_cancel₀ (torsion_ne_zero hell hζ))

@[simp] theorem torsionUnit_coe (hell : 0 < ell) (hζ : ζ ^ ell = 1) :
    ((torsionUnit (R := R) hell hζ : integralClosure R A) : A) = ζ := rfl

/-- Multiplication by the scalar preserves the entire integral closure as a set. -/
theorem torsion_smul_integralClosure (hell : 0 < ell) (hζ : ζ ^ ell = 1) :
    ζ • (integralClosure R A : Set A) = (integralClosure R A : Set A) := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (torsion_isIntegral (R := R) hell hζ).mul hy
  · intro hx
    refine ⟨ζ⁻¹ * x, (torsion_inv_isIntegral (R := R) hell hζ).mul hx, ?_⟩
    change ζ * (ζ⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ (torsion_ne_zero hell hζ), one_mul]

/-- A root-of-unity change of generator leaves every principal order set unchanged. -/
theorem torsion_smul_principal (hell : 0 < ell) (hζ : ζ ^ ell = 1) (a : A) :
    (ζ * a) • (integralClosure R A : Set A) =
      a • (integralClosure R A : Set A) := by
  rw [mul_comm ζ a, mul_smul, torsion_smul_integralClosure (R := R) hell hζ]

/-- Direct consumer of the existential root-choice output of the theta interface. -/
theorem principal_eq_of_torsion_multiple (hell : 0 < ell) {x y : A}
    (h : ∃ ζ : A, ζ ^ ell = 1 ∧ x = ζ * y) :
    x • (integralClosure R A : Set A) = y • (integralClosure R A : Set A) := by
  obtain ⟨ζ, hζ, rfl⟩ := h
  exact torsion_smul_principal hell hζ y

/-- Equal nonzero-root powers produce an actual finite-order ratio. -/
theorem ratio_pow_eq_one {x y : A} (hy : y ≠ 0) (hxy : x ^ ell = y ^ ell) :
    (x / y) ^ ell = 1 := by
  rw [div_pow, hxy, div_self (pow_ne_zero ell hy)]

/-- Equal powers of two choices imply equality of their principal order sets. -/
theorem principal_eq_of_pow_eq (hell : 0 < ell) {x y : A}
    (hy : y ≠ 0) (hxy : x ^ ell = y ^ ell) :
    x • (integralClosure R A : Set A) = y • (integralClosure R A : Set A) := by
  apply principal_eq_of_torsion_multiple hell
  exact ⟨x / y, ratio_pow_eq_one hy hxy, (div_mul_cancel₀ x hy).symm⟩

end CoreTorsionHullStability

#print axioms CoreTorsionHullStability.torsion_ne_zero
#print axioms CoreTorsionHullStability.torsion_isIntegral
#print axioms CoreTorsionHullStability.torsion_inv_isIntegral
#print axioms CoreTorsionHullStability.torsionUnit
#print axioms CoreTorsionHullStability.torsionUnit_coe
#print axioms CoreTorsionHullStability.torsion_smul_integralClosure
#print axioms CoreTorsionHullStability.torsion_smul_principal
#print axioms CoreTorsionHullStability.principal_eq_of_torsion_multiple
#print axioms CoreTorsionHullStability.ratio_pow_eq_one
#print axioms CoreTorsionHullStability.principal_eq_of_pow_eq
