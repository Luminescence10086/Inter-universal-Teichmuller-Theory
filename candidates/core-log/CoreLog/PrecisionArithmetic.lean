import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
namespace CorePrecision

theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  cases k with
  | zero => decide
  | succ k =>
    calc
      2 * (k + 1) ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k)))
      _ = 2 ^ (k + 1) := by rw [pow_succ]; omega

theorem twice_factorization_le (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    2 * n.factorization p ≤ n := by
  calc
    2 * n.factorization p ≤ 2 ^ n.factorization p := two_mul_le_two_pow _
    _ ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp.two_le _
    _ ≤ n := Nat.ordProj_le p hn

theorem log_tail_valuation_bound (p n r M : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) (hr : 1 ≤ r) (hcut : 2 * M ≤ n) :
    M ≤ n * r - n.factorization p := by
  have hv := twice_factorization_le p n hp hn
  have hm : n ≤ n * r := by simpa using Nat.mul_le_mul_left n hr
  omega

end CorePrecision
#print axioms CorePrecision.log_tail_valuation_bound
#print axioms CorePrecision.two_mul_le_two_pow
#print axioms CorePrecision.twice_factorization_le
