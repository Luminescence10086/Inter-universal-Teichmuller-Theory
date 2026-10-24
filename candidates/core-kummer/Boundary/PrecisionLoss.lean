import Boundary.DiscreteValuation

/-! Exact finite precision cost of a normalization power. Raising the comparison
level from n to m*n recovers n-divisibility of the original valuation difference.
No coprimality or entire infinite tower is needed for this finite certificate. -/
set_option autoImplicit false

namespace CoreKummerPrecision
open scoped WithZero Pointwise
open KummerTheory CoreDiscreteKummer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem exponent_sub_dvd_of_raised_level (v : Valuation K ℤᵐ⁰)
    (m n : ℕ) (hm : m ≠ 0) [HasKummerRoots (m * n) K Ω] (x y : Kˣ)
    (h : kummer (m * n) K Ω (x ^ m) = kummer (m * n) K Ω (y ^ m)) :
    (n : ℤ) ∣ exponent v (x : K) - exponent v (y : K) := by
  have hd := exponent_sub_dvd_of_power v (pow_ne_zero m x.ne_zero)
    (pow_ne_zero m y.ne_zero) (m * n)
    (power_ratio_of_kummer_eq (m * n) (x ^ m) (y ^ m) h)
  rw [exponent_pow, exponent_pow, Nat.cast_mul, ← mul_sub] at hd
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hm : (m : ℤ) ≠ 0)).mp hd

theorem principal_eq_of_raised_level_and_bound (v : Valuation K ℤᵐ⁰)
    (m n : ℕ) (hm : m ≠ 0) [HasKummerRoots (m * n) K Ω] (x y : Kˣ)
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (h : kummer (m * n) K Ω (x ^ m) = kummer (m * n) K Ω (y ^ m)) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  apply principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (exponent_sub_dvd_of_raised_level v m n hm x y h) (by simpa using hbound)

end CoreKummerPrecision

#print axioms CoreKummerPrecision.exponent_sub_dvd_of_raised_level
#print axioms CoreKummerPrecision.principal_eq_of_raised_level_and_bound
