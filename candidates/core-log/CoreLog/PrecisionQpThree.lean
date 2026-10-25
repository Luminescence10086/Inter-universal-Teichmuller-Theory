import CoreLog.Precision
import CoreLog.QpThree

/-! The finite truncation theorem specialized to Mathlib's actual `ℚ_[3]`. -/

set_option autoImplicit false

namespace CoreLog

noncomputable section

open PadicLogVolume

/-- On actual principal units of `ℚ_[3]`, the first `2 * M` logarithm terms
approximate `padicLog x` with error at most `(3 : ℝ)⁻¹ ^ M`. -/
theorem principal_unit_log_truncation_bound {x : ℚ_[3]}
    (hx : ‖x - 1‖ < 1) (M : ℕ) :
    ‖padicLog x - ∑ n ∈ Finset.range (2 * M), logTerm x n‖ ≤
      ((3 : ℝ)⁻¹) ^ M := by
  rw [← norm_three]
  simpa using norm_padicLog_sub_two_mul_sum_range_le
    (p := 3) (r := 1) (by decide : Nat.Prime 3) norm_three_lt_one
    (le_refl 1) (by simpa using principal_unit_bound hx) M

end
end CoreLog

#print axioms CoreLog.principal_unit_log_truncation_bound
