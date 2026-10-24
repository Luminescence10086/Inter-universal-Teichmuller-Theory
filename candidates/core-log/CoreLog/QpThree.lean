import PadicLogVolume.PadicLog
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! Actual Q_3 statements use Mathlib's native p-adic norm. No `open scoped Valued`
occurs here: the normed-field generalization of the upstream proof avoids a second norm. -/
namespace CoreLog
noncomputable section
open Filter Topology

instance three_prime : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem norm_three : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by
  simpa using (Padic.norm_p (p := 3))

theorem norm_three_lt_one : ‖(3 : ℚ_[3])‖ < 1 := by
  rw [norm_three]
  norm_num

theorem principal_unit_bound {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    ‖x - 1‖ ≤ ‖(3 : ℚ_[3])‖ := by
  rw [norm_three]
  have h := Padic.norm_lt_pow_iff_norm_le_pow_sub_one (x - 1) 0
  norm_num at h
  simpa only [one_div] using h.mp hx

theorem principal_unit_log_summable {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    Summable (PadicLogVolume.logTerm x) :=
  PadicLogVolume.summable_logTerm (by decide : Nat.Prime 3) norm_three_lt_one hx

theorem principal_unit_log_hasSum {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (PadicLogVolume.padicLog x) :=
  (principal_unit_log_summable hx).hasSum

theorem principal_unit_log_image :
    PadicLogVolume.padicLog '' {x : ℚ_[3] | ‖x - 1‖ < 1} =
      {y : ℚ_[3] | ‖y‖ ≤ (3 : ℝ)⁻¹} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ‖PadicLogVolume.padicLog x‖ ≤ (3 : ℝ)⁻¹
    rw [← norm_three]
    exact PadicLogVolume.norm_padicLog_le_norm_p (by decide : Nat.Prime 3)
      norm_three_lt_one (principal_unit_bound hx)
  · intro hy
    have htwo : ‖(2 : ℚ_[3])‖ = 1 :=
      PadicLogVolume.norm_two_eq_one (by decide : Nat.Prime 3) norm_three_lt_one (by decide)
    have hrad : ‖2 * (3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by
      rw [norm_mul, htwo, one_mul, norm_three]
    obtain ⟨a, ha, he⟩ := PadicLogVolume.exists_padicLog_eq
      (by decide : Nat.Prime 3) norm_three_lt_one (y := y) (by simpa [hrad] using hy)
    refine ⟨1 + a, ?_, he⟩
    change ‖1 + a - 1‖ < 1
    simpa using ha.trans_lt (PadicLogVolume.norm_two_mul_lt_one norm_three_lt_one)

theorem principal_unit_log_mul {x y : ℚ_[3]} (hx : ‖x - 1‖ < 1)
    (hy : ‖y - 1‖ < 1) :
    PadicLogVolume.padicLog (x*y) = PadicLogVolume.padicLog x + PadicLogVolume.padicLog y :=
  PadicLogVolume.padicLog_mul (by decide : Nat.Prime 3) norm_three_lt_one hx hy

#print axioms norm_three
#print axioms norm_three_lt_one
#print axioms principal_unit_bound
#print axioms principal_unit_log_summable
#print axioms principal_unit_log_hasSum
#print axioms principal_unit_log_image
#print axioms principal_unit_log_mul
end
end CoreLog


