import LocalFieldAudit.Shell
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Actual p-adic ideal filtrations

This module connects the scalar-layer interface to Mathlib's actual p-adic
integers, maximal ideal, norm, and valuation. The measurement/layer correspondence
is proved here for the base field Q_p, rather than supplied as a hypothesis.

Preservation of the unit ball remains an explicit assumption about a genuine
Q_p-linear equivalence. No actual IUT Ism element, logarithm-image identity,
ramified extension, Kummer choice, or packet is constructed by this module.
The exact valuation conclusion below is only a base-field conclusion; it must
not be transferred to ramified extensions by dropping their normalization.
-/

set_option autoImplicit false

open scoped Pointwise

namespace LocalFieldAudit.Filtration

variable (p : Nat) [hp : Fact p.Prime]

/-- The actual p-adic norm unit ball, including zero. -/
def ball : Set ℚ_[p] := {x | ‖x‖ ≤ 1}

/-- The image in Q_p of the n-th power of the actual maximal ideal of Z_p.
Only natural powers are used for ideals of Z_p. -/
def integerIdealImage (n : Nat) : Set ℚ_[p] :=
  ((↑) : ℤ_[p] → ℚ_[p]) ''
    (↑((IsLocalRing.maximalIdeal ℤ_[p]) ^ n) : Set ℤ_[p])

/-- A nonzero scalar dilate of the unit ball is exactly its norm ball.
This equivalence includes x=0 and is not a finite-valued valuation assertion. -/
theorem mem_smul_ball_iff_norm_le (a x : ℚ_[p]) (ha : a ≠ 0) :
    x ∈ a • ball p ↔ ‖x‖ ≤ ‖a‖ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖a * y‖ ≤ ‖a‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hy (norm_nonneg a)).trans_eq (mul_one _)
  · intro hx
    refine ⟨x / a, ?_, ?_⟩
    · change ‖x / a‖ ≤ 1
      rw [norm_div, div_le_one₀ (norm_pos_iff.mpr ha)]
      exact hx
    · change a * (x / a) = x
      exact mul_div_cancel₀ x ha

/-- All integer scalar layers have a proved, actual norm interpretation. -/
theorem mem_zpow_ball_iff_norm_le (n : Int) (x : ℚ_[p]) :
    x ∈ ((p : ℚ_[p]) ^ n) • ball p ↔ ‖x‖ ≤ (p : ℝ) ^ (-n) := by
  rw [mem_smul_ball_iff_norm_le p _ _ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)),
    Padic.norm_p_zpow]

/-- The valuation interpretation of those layers explicitly excludes zero. -/
theorem mem_zpow_ball_iff_le_valuation (n : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    x ∈ ((p : ℚ_[p]) ^ n) • ball p ↔ n ≤ x.valuation := by
  rw [mem_zpow_ball_iff_norm_le, Padic.norm_eq_zpow_neg_valuation hx,
    zpow_le_zpow_iff_right₀, neg_le_neg_iff]
  exact_mod_cast hp.out.one_lt

/-- Actual powers of the maximal ideal are norm layers, with zero included. -/
theorem mem_maximalIdeal_pow_iff_norm_le (n : Nat) (x : ℤ_[p]) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n ↔
      ‖x‖ ≤ (p : ℝ) ^ (-(n : Int)) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

/-- The actual ideal/valuation correspondence, with its nonzero premise. -/
theorem mem_maximalIdeal_pow_iff_le_valuation (n : Nat) (x : ℤ_[p]) (hx : x ≠ 0) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n ↔ n ≤ x.valuation := by
  rw [mem_maximalIdeal_pow_iff_norm_le]
  exact PadicInt.norm_le_pow_iff_le_valuation x hx n

/-- Coercing the actual integral ideal into Q_p gives exactly the scalar layer.
The proof constructs the integral witnesses in both directions. -/
theorem integerIdealImage_eq_pow_ball (n : Nat) :
    integerIdealImage p n = ((p : ℚ_[p]) ^ n) • ball p := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyIdeal : (y : ℤ_[p]) ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (y : ℤ_[p]) n).mp
        ((mem_maximalIdeal_pow_iff_norm_le p n (y : ℤ_[p])).mp hy)
    obtain ⟨z, hz⟩ := (Ideal.mem_span_singleton (α := ℤ_[p])).mp hyIdeal
    refine ⟨(z : ℚ_[p]), z.property, ?_⟩
    change (p : ℚ_[p]) ^ n * (z : ℚ_[p]) = x
    calc
      (p : ℚ_[p]) ^ n * (z : ℚ_[p]) = (y : ℚ_[p]) := by
        simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using
          congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz.symm
      _ = x := hxy
  · rintro ⟨y, hy, hxy⟩
    let z : ℤ_[p] := ⟨y, hy⟩
    refine ⟨(p : ℤ_[p]) ^ n * z, ?_, ?_⟩
    · change (p : ℤ_[p]) ^ n * z ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact ⟨z, rfl⟩
    · simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
        smul_eq_mul] using hxy

/-- Integer scalar layers of the actual maximal-ideal image have the strict
valuation threshold. The one-step shift from the closed unit ball is explicit. -/
theorem mem_zpow_maximalIdealImage_iff_lt_valuation
    (n : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    x ∈ ((p : ℚ_[p]) ^ n) • integerIdealImage p 1 ↔ n < x.valuation := by
  rw [integerIdealImage_eq_pow_ball, pow_one, smul_smul]
  rw [← zpow_add_one₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
  rw [mem_zpow_ball_iff_le_valuation p (n + 1) x hx, Int.add_one_le_iff]

/-- The already checked scalar-layer theorem now preserves genuine ideal images. -/
theorem preserves_integerIdealImages (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hball : e '' ball p = ball p) (n : Nat) :
    e '' integerIdealImage p n = integerIdealImage p n := by
  rw [integerIdealImage_eq_pow_ball]
  exact Shell.image_scalar_layer e (ball p) hball ((p : ℚ_[p]) ^ n)

/-- In the base field, preservation of the actual maximal-ideal image is
equivalent to preservation of the unit ball. Scalar cancellation is proved
using p nonzero; no logarithm-image identity is used. -/
theorem preserves_maximalIdealImage_iff_ball (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) :
    e '' integerIdealImage p 1 = integerIdealImage p 1 ↔ e '' ball p = ball p := by
  constructor
  · intro hm
    have hs : e '' ((p : ℚ_[p]) • ball p) = (p : ℚ_[p]) • ball p := by
      simpa only [integerIdealImage_eq_pow_ball, pow_one] using hm
    rw [Set.image_smul_comm e (p : ℚ_[p]) (ball p) (fun x => e.map_smul _ x)] at hs
    have hinj : Function.Injective (fun x : ℚ_[p] => (p : ℚ_[p]) • x) := by
      intro x y hxy
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero) hxy
    exact (Set.image_injective.mpr hinj) hs
  · intro hb
    exact preserves_integerIdealImages p e hb 1

/-- In the base field Q_p, unit-ball preservation gives exact additive valuation
preservation. No measurement correspondence is assumed. -/
theorem preserves_ball_valuation (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hball : e '' ball p = ball p) (x : ℚ_[p]) (hx : x ≠ 0) :
    (e x).valuation = x.valuation := by
  have hex : e x ≠ 0 := by
    intro hzero
    apply hx
    apply e.injective
    simpa using hzero
  have levels (n : Int) : n ≤ (e x).valuation ↔ n ≤ x.valuation :=
    (mem_zpow_ball_iff_le_valuation p n (e x) hex).symm.trans
      ((Shell.scalar_layer_membership_iff e (ball p) hball ((p : ℚ_[p]) ^ n) x).trans
        (mem_zpow_ball_iff_le_valuation p n x hx))
  exact le_antisymm ((levels _).mp le_rfl) ((levels _).mpr le_rfl)

/-- Norm preservation includes zero, handled separately from finite valuation. -/
theorem preserves_ball_norm (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hball : e '' ball p = ball p) (x : ℚ_[p]) : ‖e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hex : e x ≠ 0 := by
      intro hzero
      apply hx
      apply e.injective
      simpa using hzero
    rw [Padic.norm_eq_zpow_neg_valuation hex, Padic.norm_eq_zpow_neg_valuation hx,
      preserves_ball_valuation p e hball x hx]

/-- An end-to-end norm consequence of preserving the actual base-field maximal
ideal image, with no measurement/layer hypothesis. -/
theorem preserves_maximalIdealImage_norm (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hm : e '' integerIdealImage p 1 = integerIdealImage p 1) (x : ℚ_[p]) :
    ‖e x‖ = ‖x‖ := by
  exact preserves_ball_norm p e ((preserves_maximalIdealImage_iff_ball p e).mp hm) x

/-- Instantiate the previous round's strict-threshold interface using a proved
actual ideal/valuation correspondence instead of assuming that correspondence. -/
theorem preserves_maximalIdealImage_strict_threshold
    (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hm : e '' integerIdealImage p 1 = integerIdealImage p 1)
    (x : ℚ_[p]) (hx : x ≠ 0) (n : Int) :
    n < (e x).valuation ↔ n < x.valuation := by
  exact Shell.threshold_iff_of_layers e (integerIdealImage p 1) hm
    (fun m => (p : ℚ_[p]) ^ m) (fun m => m) Padic.valuation
    (fun m y hy => mem_zpow_maximalIdealImage_iff_lt_valuation p m y hy) x hx n

/-- A genuine Q_p-linear equivalence can map the ball strictly inside itself.
Thus a one-sided lattice inclusion is insufficient for the preservation results.
This is a base-field example, not an assertion about the actual IUT Ism group. -/
theorem p_scaling_strict_ball_contraction :
    ∃ e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p],
      e '' ball p ⊆ ball p ∧ e '' ball p ≠ ball p ∧ ‖e 1‖ ≠ 1 := by
  let e := LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have he (x : ℚ_[p]) : e x = (p : ℚ_[p]) * x := rfl
  have hbound : ∀ x ∈ ball p, ‖e x‖ < 1 := by
    intro x hx
    rw [he, norm_mul]
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_left hx (norm_nonneg (p : ℚ_[p]))).trans_eq (mul_one _))
      Padic.norm_p_lt_one
  refine ⟨e, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact (hbound x hx).le
  · intro hall
    have hmem : (1 : ℚ_[p]) ∈ e '' ball p := by
      rw [hall]
      change ‖(1 : ℚ_[p])‖ ≤ 1
      simp
    obtain ⟨x, hx, heq⟩ := hmem
    have hlt := hbound x hx
    rw [heq, norm_one] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  · rw [he, mul_one]
    exact ne_of_lt Padic.norm_p_lt_one

end LocalFieldAudit.Filtration
