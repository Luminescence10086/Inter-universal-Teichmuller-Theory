/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: LANA Project; local sphere descent and gluing by Codex

The finite-zero contradiction is adapted from
TateCurvesTheta/Theta/LaurentSphere.lean:143-167 at upstream commit
 d1fba94861c886b671f4137ab35e24b7474c9e00.
Unlike that global uniqueness theorem, this module assumes summability only at
one nonzero radius and equality only on that sphere. It uses the proved local
StrassmannSphere.finite_zeros, not global Laurent coefficient uniqueness.
-/
import TateCurvesTheta.Theta.LaurentUnitSphere

/-! Coefficient descent on a single sphere and along an integer-indexed atlas.
No global summability, annulus covering, theta automorphy, or common coefficient
family is assumed in the sphere comparison theorem. -/
set_option autoImplicit false
noncomputable section

namespace CoreSphereCoefficientDescent

open TateCurvesTheta TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Two Laurent expansions agree coefficientwise if their weighted coefficients
are summable at one radius and their values agree on the corresponding sphere.
The Tate parameter supplies infinitely many distinct norm-one witnesses. -/
theorem coeff_eq_of_sphere_values
    (t : TateParameter K) (a b : ℤ → K) (r : Kˣ)
    (ha : Summable (fun n : ℤ => a n * (r : K) ^ n))
    (hb : Summable (fun n : ℤ => b n * (r : K) ^ n))
    (heq : ∀ v : Kˣ, ‖(v : K)‖ = 1 →
      (∑' n : ℤ, a n * ((r * v : Kˣ) : K) ^ n) =
        ∑' n : ℤ, b n * ((r * v : Kˣ) : K) ^ n) :
    a = b := by
  let A : ℤ → K := fun n => a n * (r : K) ^ n
  let B : ℤ → K := fun n => b n * (r : K) ^ n
  let c : ℤ → K := A - B
  have hA : Summable A := ha
  have hB : Summable B := hb
  have hc : Summable c := hA.sub hB
  have hzero : ∀ v : Kˣ, ‖(v : K)‖ = 1 →
      (∑' n : ℤ, c n * (v : K) ^ n) = 0 := by
    intro v hv
    have hAv := StrassmannSphere.summable_mul_zpow hA hv
    have hBv := StrassmannSphere.summable_mul_zpow hB hv
    have heqA : (∑' n : ℤ, A n * (v : K) ^ n) =
        ∑' n : ℤ, a n * ((r * v : Kˣ) : K) ^ n := by
      refine tsum_congr fun n => ?_
      simp only [A, Units.val_mul, mul_zpow]
      ring
    have heqB : (∑' n : ℤ, B n * (v : K) ^ n) =
        ∑' n : ℤ, b n * ((r * v : Kˣ) : K) ^ n := by
      refine tsum_congr fun n => ?_
      simp only [B, Units.val_mul, mul_zpow]
      ring
    have hsplit : (∑' n : ℤ, c n * (v : K) ^ n) =
        (∑' n : ℤ, A n * (v : K) ^ n) -
          (∑' n : ℤ, B n * (v : K) ^ n) := by
      rw [← hAv.tsum_sub hBv]
      exact tsum_congr fun n => by simp only [c, Pi.sub_apply, sub_mul]
    rw [hsplit, heqA, heqB, heq v hv, sub_self]
  have hc0 : c = 0 := by
    by_contra hcne
    have hfin := StrassmannSphere.finite_zeros hc hcne
    have hinj : Function.Injective (fun k : ℕ => (t.sphereWitness k : K)) := by
      intro j k h
      exact t.sphereWitness_injective (Units.ext h)
    have hmem : ∀ k : ℕ, (t.sphereWitness k : K) ∈
        {v : K | ‖v‖ = 1 ∧ (∑' n : ℤ, c n * v ^ n) = 0} := by
      intro k
      have hnorm : ‖(t.sphereWitness k : K)‖ = 1 := by
        rw [sphereWitness_val]
        exact t.norm_one_add_qpow k
      exact ⟨hnorm, hzero (t.sphereWitness k) hnorm⟩
    exact (Set.infinite_of_injective_forall_mem hinj hmem) hfin
  funext n
  have hn := congrFun hc0 n
  change a n * (r : K) ^ n - b n * (r : K) ^ n = 0 at hn
  exact mul_right_cancel₀ (zpow_ne_zero n r.ne_zero) (sub_eq_zero.mp hn)

/-- Equality across each neighboring pair of integer indices glues the family
into its value at zero. This lemma is purely about the index set. -/
theorem family_eq_zero_of_eq_succ {α : Type*} (f : ℤ → α)
    (h : ∀ m : ℤ, f (m + 1) = f m) (m : ℤ) : f m = f 0 := by
  induction m using Int.induction_on with
  | zero => rfl
  | succ i ih => exact (h (i : ℤ)).trans ih
  | pred i ih =>
      have hstep : f (-(i : ℤ)) = f (-(i : ℤ) - 1) := by
        simpa using h (-(i : ℤ) - 1)
      exact hstep.symm.trans ih

/-- Local expansions glued on one sphere for each adjacent pair have a single
coefficient family. Each summability premise concerns only its overlap radius. -/
theorem coefficients_eq_of_adjacent_sphere_values
    (t : TateParameter K) (B : ℤ → ℤ → K) (r : ℤ → Kˣ)
    (hleft : ∀ m : ℤ, Summable (fun n : ℤ => B m n * (r m : K) ^ n))
    (hright : ∀ m : ℤ, Summable (fun n : ℤ => B (m + 1) n * (r m : K) ^ n))
    (hoverlap : ∀ (m : ℤ) (v : Kˣ), ‖(v : K)‖ = 1 →
      (∑' n : ℤ, B m n * ((r m * v : Kˣ) : K) ^ n) =
        ∑' n : ℤ, B (m + 1) n * ((r m * v : Kˣ) : K) ^ n)
    (m : ℤ) : B m = B 0 := by
  apply family_eq_zero_of_eq_succ B _ m
  intro j
  exact (coeff_eq_of_sphere_values t (B j) (B (j + 1)) (r j)
    (hleft j) (hright j) (hoverlap j)).symm

end CoreSphereCoefficientDescent

#print axioms CoreSphereCoefficientDescent.coeff_eq_of_sphere_values
#print axioms CoreSphereCoefficientDescent.family_eq_zero_of_eq_succ
#print axioms CoreSphereCoefficientDescent.coefficients_eq_of_adjacent_sphere_values