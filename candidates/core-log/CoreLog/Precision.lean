import CoreLog.PrecisionArithmetic
import PadicLogVolume.PadicLog

/-!
# Finite truncation bounds for the `p`-adic logarithm

The integer valuation estimate in `CoreLog.PrecisionArithmetic` is joined here
to the analytic logarithm series.  The tail bound uses the ultrametric
inequality; it does not assume absolute (real-norm) summability.
-/

set_option autoImplicit false

namespace CoreLog

open PadicLogVolume

universe u

noncomputable section

variable {k : Type u} [NormedField k] [IsUltrametricDist k]
variable {p : ℕ}

/-- Once `2 * M ≤ n + 1`, the `n`-th logarithm term has norm at most
`‖p‖ ^ M`, provided `‖x - 1‖ ≤ ‖p‖ ^ r` and `r ≥ 1`. -/
theorem norm_logTerm_le_pow_of_two_mul_le [CharZero k]
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {r : ℕ} (hr : 1 ≤ r)
    {x : k} (hx : ‖x - 1‖ ≤ ‖(p : k)‖ ^ r) {M n : ℕ}
    (hn : 2 * M ≤ n + 1) : ‖logTerm x n‖ ≤ ‖(p : k)‖ ^ M := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hfac_lt : (n + 1).factorization p < n + 1 :=
    factorization_lt_self hp (Nat.succ_ne_zero n)
  have hfac_le : (n + 1).factorization p ≤ r * (n + 1) := by
    calc
      (n + 1).factorization p ≤ n + 1 := hfac_lt.le
      _ = 1 * (n + 1) := (one_mul _).symm
      _ ≤ r * (n + 1) := Nat.mul_le_mul_right _ hr
  have hvaluation : M ≤ (n + 1) * r - (n + 1).factorization p :=
    CorePrecision.log_tail_valuation_bound p (n + 1) r M hp
      (Nat.succ_ne_zero n) hr hn
  have hvaluation' : M ≤ r * (n + 1) - (n + 1).factorization p := by
    simpa [Nat.mul_comm] using hvaluation
  rw [norm_logTerm, norm_natCast_eq_pow hp hpk (Nat.succ_ne_zero n)]
  calc
    ‖x - 1‖ ^ (n + 1) * (‖(p : k)‖ ^ (n + 1).factorization p)⁻¹
        ≤ (‖(p : k)‖ ^ r) ^ (n + 1) *
            (‖(p : k)‖ ^ (n + 1).factorization p)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = ‖(p : k)‖ ^ (r * (n + 1)) *
          (‖(p : k)‖ ^ (n + 1).factorization p)⁻¹ := by
      rw [← pow_mul]
    _ = ‖(p : k)‖ ^ (r * (n + 1) - (n + 1).factorization p) := by
      rw [← pow_sub₀ _ hp0.ne' hfac_le]
    _ ≤ ‖(p : k)‖ ^ M :=
      pow_le_pow_of_le_one (norm_nonneg _) hpk.le hvaluation'

/-- Discarding the first `N` logarithm terms costs at most `‖p‖ ^ M`
when `2 * M ≤ N`.  The right-hand side is independent of `x`. -/
theorem norm_padicLog_sub_sum_range_le [CharZero k] [CompleteSpace k]
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {r : ℕ} (hr : 1 ≤ r)
    {x : k} (hx : ‖x - 1‖ ≤ ‖(p : k)‖ ^ r) {M N : ℕ}
    (hN : 2 * M ≤ N) :
    ‖padicLog x - ∑ n ∈ Finset.range N, logTerm x n‖ ≤ ‖(p : k)‖ ^ M := by
  have hx' : ‖x - 1‖ < 1 := by
    calc
      ‖x - 1‖ ≤ ‖(p : k)‖ ^ r := hx
      _ ≤ ‖(p : k)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hpk.le hr
      _ < 1 := by simpa using hpk
  have hs : Summable (logTerm x) := summable_logTerm hp hpk hx'
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : padicLog x - ∑ n ∈ Finset.range N, logTerm x n =
      ∑' n : ℕ, logTerm x (n + N) := by
    rw [padicLog, ← hsplit]
    simp
  rw [htail]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (fun n => norm_logTerm_le_pow_of_two_mul_le hp hpk hr hx (by omega))

/-- The canonical `2 * M`-term truncation has error at most `‖p‖ ^ M`. -/
theorem norm_padicLog_sub_two_mul_sum_range_le [CharZero k] [CompleteSpace k]
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {r : ℕ} (hr : 1 ≤ r)
    {x : k} (hx : ‖x - 1‖ ≤ ‖(p : k)‖ ^ r) (M : ℕ) :
    ‖padicLog x - ∑ n ∈ Finset.range (2 * M), logTerm x n‖ ≤ ‖(p : k)‖ ^ M :=
  norm_padicLog_sub_sum_range_le hp hpk hr hx (le_refl _)

end
end CoreLog

#print axioms CoreLog.norm_logTerm_le_pow_of_two_mul_le
#print axioms CoreLog.norm_padicLog_sub_sum_range_le
#print axioms CoreLog.norm_padicLog_sub_two_mul_sum_range_le
