/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: LANA Project; local generalization by Codex

The recurrence and integer-induction proofs below are adapted from
TateCurvesTheta/Theta/ThetaProdLaurent.lean:125-211, upstream commit
 d1fba94861c886b671f4137ab35e24b7474c9e00.
The upstream theorem treats thetaProd; here the input is an arbitrary globally
summable Laurent family with the actual q-translation law. Coefficient uniqueness
is supplied by the proved TateParameter.laurentCoeffUnique, not an extra premise.
-/
import TateCurvesTheta.Theta.LaurentUnitSphere

/-! Global theta rigidity from Laurent coefficients and deck automorphy.
The shared scalar is a conclusion. No scalar-comparison or closed-coefficient
identity is stored as input. This is a fixed Tate-coordinate theorem, not an
identification with an abstract tempered theta section. -/
set_option autoImplicit false
noncomputable section

namespace CoreGlobalThetaRigidity

open TateCurvesTheta TateCurvesTheta.TateParameter

private lemma thetaExp_add_one (n : ℤ) :
    thetaExp (n + 1) = thetaExp n + (n + 1) := by
  rw [thetaExp_add, thetaExp_one]
  ring

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K) (b : ℤ → K)

/-- The function of one globally defined Laurent coefficient family. -/
def laurentValue (u : Kˣ) : K := ∑' n : ℤ, b n * (u : K) ^ n

variable
  (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n))
  (hauto : ∀ u : Kˣ,
    (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
      ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))

include hsum hauto

/-- Comparing the two global Laurent expansions of the translated function gives
its coefficient recursion. The uniqueness principle is an imported theorem. -/
theorem laurent_coeff_recurrence (n : ℤ) :
    b (n + 1) = (t.q : K) ^ (n + 1) * b n := by
  have hqne : (t.q : K) ≠ 0 := t.q.ne_zero
  have hAsum : ∀ v : Kˣ, Summable
      (fun k : ℤ => (b k * (t.q : K) ^ k) * (v : K) ^ k) := by
    intro v
    refine (hsum (t.q * v)).congr fun k => ?_
    rw [Units.val_mul, mul_zpow]
    ring
  have hBsum : ∀ v : Kˣ, Summable
      (fun k : ℤ => (b (k + 1) * (t.q : K)⁻¹) * (v : K) ^ k) := by
    intro v
    have h1 : Summable (fun k : ℤ => b (k + 1) * (v : K) ^ (k + 1)) :=
      (hsum v).comp_injective (i := fun k : ℤ => k + 1) fun a c h => by simpa using h
    have h2 : Summable (fun k : ℤ => b (k + 1) * (v : K) ^ k) := by
      refine (h1.mul_right (v : K)⁻¹).congr fun k => ?_
      rw [mul_assoc, zpow_add_one₀ v.ne_zero, mul_assoc, mul_inv_cancel₀ v.ne_zero, mul_one]
    refine (h2.mul_left (t.q : K)⁻¹).congr fun k => ?_
    ring
  have hAeq : ∀ v : Kˣ,
      (∑' k : ℤ, (b k * (t.q : K) ^ k) * (v : K) ^ k) =
        ∑' k : ℤ, b k * ((t.q * v : Kˣ) : K) ^ k := by
    intro v
    refine tsum_congr fun k => ?_
    rw [Units.val_mul, mul_zpow]
    ring
  have hshift : ∀ v : Kˣ,
      (∑' k : ℤ, b (k + 1) * (v : K) ^ k) =
        (v : K)⁻¹ * (∑' k : ℤ, b k * (v : K) ^ k) := by
    intro v
    have key : (∑' k : ℤ, b (k + 1) * (v : K) ^ k) =
        ∑' k : ℤ, b k * (v : K) ^ k * (v : K)⁻¹ := by
      rw [← Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
        (fun k => b k * (v : K) ^ k * (v : K)⁻¹)]
      refine tsum_congr fun k => ?_
      simp only [Equiv.coe_addRight]
      rw [mul_assoc]
      congr 1
      rw [zpow_add_one₀ v.ne_zero, mul_assoc, mul_inv_cancel₀ v.ne_zero, mul_one]
    rw [key, tsum_mul_right, mul_comm]
  have hBeq : ∀ v : Kˣ,
      (∑' k : ℤ, (b (k + 1) * (t.q : K)⁻¹) * (v : K) ^ k) =
        ∑' k : ℤ, b k * ((t.q * v : Kˣ) : K) ^ k := by
    intro v
    have hpull : (∑' k : ℤ, (b (k + 1) * (t.q : K)⁻¹) * (v : K) ^ k) =
        (t.q : K)⁻¹ * (∑' k : ℤ, b (k + 1) * (v : K) ^ k) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by ring
    rw [hpull, hshift v, Units.val_mul, hauto v, mul_inv]
    ring
  have hAB : (fun k : ℤ => b k * (t.q : K) ^ k) =
      (fun k : ℤ => b (k + 1) * (t.q : K)⁻¹) :=
    t.laurentCoeffUnique _ _ hAsum hBsum (fun v => by rw [hAeq v, hBeq v])
  have hABn : b n * (t.q : K) ^ n = b (n + 1) * (t.q : K)⁻¹ := congrFun hAB n
  calc
    b (n + 1) = b (n + 1) * (t.q : K)⁻¹ * (t.q : K) := by
      rw [mul_assoc, inv_mul_cancel₀ hqne, mul_one]
    _ = b n * (t.q : K) ^ n * (t.q : K) := by rw [← hABn]
    _ = b n * ((t.q : K) ^ n * (t.q : K)) := by ring
    _ = b n * (t.q : K) ^ (n + 1) := by rw [← zpow_add_one₀ hqne]
    _ = (t.q : K) ^ (n + 1) * b n := by ring

/-- The global deck equation determines every Laurent coefficient from b 0. -/
theorem laurent_coeff_eq_theta_coeff (n : ℤ) :
    b n = b 0 * (t.q : K) ^ thetaExp n := by
  have hqne : (t.q : K) ≠ 0 := t.q.ne_zero
  have hrec := laurent_coeff_recurrence t b hsum hauto
  induction n using Int.induction_on with
  | zero => simp [thetaExp]
  | succ i ih =>
      have hts : thetaExp ((i : ℤ) + 1) = thetaExp (i : ℤ) + ((i : ℤ) + 1) :=
        thetaExp_add_one (i : ℤ)
      rw [hrec (i : ℤ), ih, hts, zpow_add₀ hqne (thetaExp (i : ℤ)) ((i : ℤ) + 1)]
      ring
  | pred i ih =>
      have hr : b (-(i : ℤ)) = (t.q : K) ^ (-(i : ℤ)) * b (-(i : ℤ) - 1) := by
        have h := hrec (-(i : ℤ) - 1)
        simpa using h
      have hstep : b (-(i : ℤ) - 1) = (t.q : K) ^ (i : ℤ) * b (-(i : ℤ)) := by
        rw [hr, ← mul_assoc, ← zpow_add₀ hqne]
        simp
      have hts : thetaExp (-(i : ℤ) - 1) = thetaExp (-(i : ℤ)) + (i : ℤ) := by
        have h := thetaExp_add_one (-(i : ℤ) - 1)
        simp only [sub_add_cancel] at h
        omega
      rw [hstep, ih, hts, zpow_add₀ hqne (thetaExp (-(i : ℤ))) (i : ℤ)]
      ring

/-- All values of the source Laurent family share the same scalar b 0. -/
theorem laurentValue_eq_const_mul_theta (u : Kˣ) :
    laurentValue b u = b 0 * t.theta u := by
  rw [laurentValue, theta_apply, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [laurent_coeff_eq_theta_coeff t b hsum hauto n]
  ring

/-- The common scalar and all-point equality are derived, not part of the input. -/
theorem exists_common_scalar :
    ∃ c : K, c = b 0 ∧ ∀ u : Kˣ, laurentValue b u = c * t.theta u :=
  ⟨b 0, rfl, laurentValue_eq_const_mul_theta t b hsum hauto⟩

/-- The first two global Laurent coefficients retain the actual Tate parameter. -/
theorem laurent_coeff_one_div_zero (hb0 : b 0 ≠ 0) : b 1 / b 0 = (t.q : K) := by
  rw [laurent_coeff_eq_theta_coeff t b hsum hauto 1, thetaExp_one, zpow_one]
  exact mul_div_cancel_left₀ (t.q : K) hb0

end CoreGlobalThetaRigidity

#print axioms CoreGlobalThetaRigidity.laurent_coeff_recurrence
#print axioms CoreGlobalThetaRigidity.laurent_coeff_eq_theta_coeff
#print axioms CoreGlobalThetaRigidity.laurentValue_eq_const_mul_theta
#print axioms CoreGlobalThetaRigidity.exists_common_scalar
#print axioms CoreGlobalThetaRigidity.laurent_coeff_one_div_zero
