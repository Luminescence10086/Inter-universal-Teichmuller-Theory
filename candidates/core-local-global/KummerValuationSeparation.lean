import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Tactic

/-!
# Discrete valuation separation for actual p-adic power-class data

Source motivation: LANA Project, Apache 2.0,
`Iut/EtaleTheta/KummerClass.lean`, `decomposition_kummer_etaleThetaGerm`,
commit f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb.
That theorem identifies a restricted germ class with an inflated value class.
This file does not assert that inflation is injective or port continuous H1.
It consumes the explicit power witness that Kummer exactness would supply in
an appropriate same-field class comparison. Finite precision alone is not enough:
the finite certificate also requires an independent integer valuation bound.
-/
set_option autoImplicit false

namespace CoreKummerValuationSeparation

open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]}

/-- An actual nth-power ratio gives divisibility of the discrete valuation difference. -/
theorem valuation_sub_dvd_of_power (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (h : ∃ z : ℚ_[p], x / y = z ^ n) :
    (n : ℤ) ∣ x.valuation - y.valuation := by
  obtain ⟨z, hz⟩ := h
  have hv : (x / y).valuation = x.valuation - y.valuation := by
    rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hy), Padic.valuation_inv]
    rfl
  refine ⟨z.valuation, ?_⟩
  rw [← hv, hz, Padic.valuation_pow]

/-- A finite Kummer-power certificate separates valuations only with a strict bound. -/
theorem valuation_eq_of_bounded_power (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (hbound : (x.valuation - y.valuation).natAbs < n)
    (h : ∃ z : ℚ_[p], x / y = z ^ n) : x.valuation = y.valuation := by
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (valuation_sub_dvd_of_power hx hy n h) (by simpa using hbound)

/-- Unbounded available power levels force equality, by discreteness in ℤ. -/
theorem valuation_eq_of_unbounded_powers (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ z : ℚ_[p], x / y = z ^ n) :
    x.valuation = y.valuation := by
  obtain ⟨n, hn, hz⟩ := h (x.valuation - y.valuation).natAbs
  exact valuation_eq_of_bounded_power hx hy n hn hz

/-- All positive finite levels suffice; no root-of-unity conclusion is claimed. -/
theorem valuation_eq_of_all_powers (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ n : ℕ, 0 < n → ∃ z : ℚ_[p], x / y = z ^ n) :
    x.valuation = y.valuation := by
  apply valuation_eq_of_unbounded_powers hx hy
  intro B
  exact ⟨B + 1, Nat.lt_succ_self B, h (B + 1) (Nat.succ_pos B)⟩

/-- One unbounded ell-adic tower suffices; ell need only be greater than one. -/
theorem valuation_eq_of_power_tower (hx : x ≠ 0) (hy : y ≠ 0)
    (ell : ℕ) (hell : 1 < ell)
    (h : ∀ k : ℕ, ∃ z : ℚ_[p], x / y = z ^ (ell ^ k)) :
    x.valuation = y.valuation := by
  apply valuation_eq_of_unbounded_powers hx hy
  intro B
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hell
  exact ⟨ell ^ k, hk, h k⟩

/-- The actual coefficient region, as the image of the genuine p-adic integer ring. -/
def integerRegion (p : ℕ) [Fact p.Prime] : Set ℚ_[p] :=
  Set.range (fun a : ℤ_[p] => (a : ℚ_[p]))

theorem mem_integerRegion (z : ℚ_[p]) : z ∈ integerRegion p ↔ ‖z‖ ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

/-- Principal p-adic integer sets are the actual closed balls of the generator's radius. -/
theorem mem_principal_iff (hx : x ≠ 0) (z : ℚ_[p]) :
    z ∈ x • integerRegion p ↔ ‖z‖ ≤ ‖x‖ := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ‖x * a‖ ≤ ‖x‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg x) ((mem_integerRegion a).mp ha)
  · intro hz
    refine ⟨z / x, (mem_integerRegion _).mpr ?_, ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hx)]
      exact hz
    · change x * (z / x) = z
      exact mul_div_cancel₀ z hx

/-- Equality of integer valuations identifies actual principal p-adic integer sets. -/
theorem principal_eq_of_valuation_eq (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : x.valuation = y.valuation) : x • integerRegion p = y • integerRegion p := by
  have hn : ‖x‖ = ‖y‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy, hv]
  ext z
  rw [mem_principal_iff hx, mem_principal_iff hy, hn]

/-- A usable finite certificate: actual power witness plus independent valuation bound. -/
theorem principal_eq_of_bounded_power (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (hbound : (x.valuation - y.valuation).natAbs < n)
    (h : ∃ z : ℚ_[p], x / y = z ^ n) :
    x • integerRegion p = y • integerRegion p :=
  principal_eq_of_valuation_eq hx hy (valuation_eq_of_bounded_power hx hy n hbound h)

theorem principal_eq_of_unbounded_powers (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ z : ℚ_[p], x / y = z ^ n) :
    x • integerRegion p = y • integerRegion p :=
  principal_eq_of_valuation_eq hx hy (valuation_eq_of_unbounded_powers hx hy h)

/-- An independently supplied bound M determines a sufficient finite precision n > M. -/
theorem principal_eq_of_power_and_bound (hx : x ≠ 0) (hy : y ≠ 0) (M n : ℕ)
    (hbound : (x.valuation - y.valuation).natAbs ≤ M) (hn : M < n)
    (h : ∃ z : ℚ_[p], x / y = z ^ n) :
    x • integerRegion p = y • integerRegion p :=
  principal_eq_of_bounded_power hx hy n (hbound.trans_lt hn) h

theorem principal_eq_of_power_tower (hx : x ≠ 0) (hy : y ≠ 0)
    (ell : ℕ) (hell : 1 < ell)
    (h : ∀ k : ℕ, ∃ z : ℚ_[p], x / y = z ^ (ell ^ k)) :
    x • integerRegion p = y • integerRegion p :=
  principal_eq_of_valuation_eq hx hy (valuation_eq_of_power_tower hx hy ell hell h)

end CoreKummerValuationSeparation

#print axioms CoreKummerValuationSeparation.valuation_sub_dvd_of_power
#print axioms CoreKummerValuationSeparation.valuation_eq_of_bounded_power
#print axioms CoreKummerValuationSeparation.valuation_eq_of_unbounded_powers
#print axioms CoreKummerValuationSeparation.valuation_eq_of_all_powers
#print axioms CoreKummerValuationSeparation.valuation_eq_of_power_tower
#print axioms CoreKummerValuationSeparation.integerRegion
#print axioms CoreKummerValuationSeparation.mem_integerRegion
#print axioms CoreKummerValuationSeparation.mem_principal_iff
#print axioms CoreKummerValuationSeparation.principal_eq_of_valuation_eq
#print axioms CoreKummerValuationSeparation.principal_eq_of_bounded_power
#print axioms CoreKummerValuationSeparation.principal_eq_of_unbounded_powers
#print axioms CoreKummerValuationSeparation.principal_eq_of_power_and_bound
#print axioms CoreKummerValuationSeparation.principal_eq_of_power_tower
