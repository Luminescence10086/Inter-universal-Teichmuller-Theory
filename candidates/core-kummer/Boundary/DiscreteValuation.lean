import ContinuousKummerTheory.Kummer.Equiv
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Tactic

/-! Kummer separation over any integer-valued field, including genuine finite-place
completions. No assumption that the field equals Qp or has ramification index one.
The log below is the integer exponent of a multiplicative valuation, not real log. -/
set_option autoImplicit false

namespace CoreDiscreteKummer
open scoped WithZero Pointwise
open KummerTheory

variable {K : Type*} [Field K]

def exponent (v : Valuation K ℤᵐ⁰) (x : K) : ℤ := WithZero.log (v x)

theorem exponent_pow (v : Valuation K ℤᵐ⁰) (x : K) (n : ℕ) :
    exponent v (x ^ n) = (n : ℤ) * exponent v x := by
  simp [exponent, map_pow, WithZero.log_pow]

theorem exponent_sub_dvd_of_power (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (h : ∃ z : K, x / y = z ^ n) :
    (n : ℤ) ∣ exponent v x - exponent v y := by
  obtain ⟨z, hz⟩ := h
  have hv : exponent v (x / y) = exponent v x - exponent v y := by
    simp only [exponent, map_div₀, WithZero.log_div (v.ne_zero_iff.mpr hx)
      (v.ne_zero_iff.mpr hy)]
  refine ⟨exponent v z, ?_⟩
  rw [← hv, hz, exponent_pow]

theorem exponent_eq_of_bounded_power (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (hbound : (exponent v x - exponent v y).natAbs < n)
    (h : ∃ z : K, x / y = z ^ n) : exponent v x = exponent v y := by
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (exponent_sub_dvd_of_power v hx hy n h) (by simpa using hbound)

theorem exponent_eq_of_power_tower (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (h : ∀ k : ℕ, ∃ z : K, x / y = z ^ (ell ^ k)) :
    exponent v x = exponent v y := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (exponent v x - exponent v y).natAbs hell
  exact exponent_eq_of_bounded_power v hx hy (ell ^ k) hk (h k)

theorem valuation_eq_of_exponent_eq (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : exponent v x = exponent v y) : v x = v y := by
  have := congrArg (WithZero.exp : ℤ → ℤᵐ⁰) h
  simpa only [exponent, WithZero.exp_log (v.ne_zero_iff.mpr hx),
    WithZero.exp_log (v.ne_zero_iff.mpr hy)] using this

/-- The actual valuation subring, not an independently postulated lattice. -/
def integerRegion (v : Valuation K ℤᵐ⁰) : Set K := v.valuationSubring

theorem mem_principal_iff (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) (z : K) :
    z ∈ x • integerRegion v ↔ v z ≤ v x := by
  have hmem : z ∈ x • integerRegion v ↔ z / x ∈ integerRegion v := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa only [smul_eq_mul, mul_div_cancel_left₀ a hx] using ha
    · intro h
      exact ⟨z / x, h, by
        change x * (z / x) = z
        exact mul_div_cancel₀ z hx⟩
  rw [hmem]
  change v (z / x) ≤ 1 ↔ v z ≤ v x
  rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hx))]

theorem principal_eq_of_exponent_eq (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : exponent v x = exponent v y) :
    x • integerRegion v = y • integerRegion v := by
  ext z
  rw [mem_principal_iff v hx, mem_principal_iff v hy,
    valuation_eq_of_exponent_eq v hx hy h]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem power_ratio_of_kummer_eq (n : ℕ) [HasKummerRoots n K Ω]
    (x y : Kˣ) (h : kummer n K Ω x = kummer n K Ω y) :
    ∃ z : K, (x : K) / (y : K) = z ^ n := by
  have hker : x / y ∈ (kummer n K Ω).ker := by
    rw [MonoidHom.mem_ker, map_div, h, div_self']
  rw [ker_kummer] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨(z : K), ?_⟩
  simpa only [powMonoidHom_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    using (congrArg (fun u : Kˣ => (u : K)) hz).symm

theorem principal_eq_of_kummer_eq_and_bound (v : Valuation K ℤᵐ⁰)
    (n : ℕ) [HasKummerRoots n K Ω] (x y : Kˣ)
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (h : kummer n K Ω x = kummer n K Ω y) :
    (x : K) • integerRegion v = (y : K) • integerRegion v :=
  principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
    (exponent_eq_of_bounded_power v x.ne_zero y.ne_zero n hbound
      (power_ratio_of_kummer_eq n x y h))

theorem principal_eq_of_normalized_kummer_tower (v : Valuation K ℤᵐ⁰)
    (m : ℕ) (hm : m ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) K Ω) (x y : Kˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) K Ω (x ^ m) = kummer (ell ^ k) K Ω (y ^ m)) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  have hv : exponent v ((x : K) ^ m) = exponent v ((y : K) ^ m) := by
    apply exponent_eq_of_power_tower v (pow_ne_zero m x.ne_zero)
      (pow_ne_zero m y.ne_zero) ell hell
    intro k
    let _ := roots k
    simpa only [Units.val_pow_eq_pow_val] using
      power_ratio_of_kummer_eq (ell ^ k) (x ^ m) (y ^ m) (h k)
  rw [exponent_pow, exponent_pow] at hv
  exact principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
    (mul_left_cancel₀ (by exact_mod_cast hm : (m : ℤ) ≠ 0) hv)

end CoreDiscreteKummer

#print axioms CoreDiscreteKummer.exponent
#print axioms CoreDiscreteKummer.exponent_pow
#print axioms CoreDiscreteKummer.exponent_sub_dvd_of_power
#print axioms CoreDiscreteKummer.exponent_eq_of_bounded_power
#print axioms CoreDiscreteKummer.exponent_eq_of_power_tower
#print axioms CoreDiscreteKummer.valuation_eq_of_exponent_eq
#print axioms CoreDiscreteKummer.integerRegion
#print axioms CoreDiscreteKummer.mem_principal_iff
#print axioms CoreDiscreteKummer.principal_eq_of_exponent_eq
#print axioms CoreDiscreteKummer.power_ratio_of_kummer_eq
#print axioms CoreDiscreteKummer.principal_eq_of_kummer_eq_and_bound
#print axioms CoreDiscreteKummer.principal_eq_of_normalized_kummer_tower
