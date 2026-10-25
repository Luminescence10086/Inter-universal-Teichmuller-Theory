import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Algebra.Order.Archimedean.Basic
import TateCurvesTheta.QParameter.Basic

/-! Laurent convergence on closed annuli from two endpoint tests.
Summability in K is used only through cofinite convergence to zero; no assertion
of summability of the real-valued family of term norms is made. The q-annuli
have inner radius ||q||^(m+1) and outer radius ||q||^(m-1). -/
set_option autoImplicit false
noncomputable section

namespace CoreAnnularConvergence

open Filter Topology TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- A closed annulus in the multiplicative q-atlas. -/
def InQClosedAnnulus (t : TateParameter K) (m : ℤ) (u : Kˣ) : Prop :=
  ‖(t.q : K)‖ ^ (m + 1) ≤ ‖(u : K)‖ ∧
    ‖(u : K)‖ ≤ ‖(t.q : K)‖ ^ (m - 1)

/-- Nonnegative exponents are controlled by the outer endpoint, and negative
exponents by the inner endpoint. Two endpoint summability tests suffice. -/
theorem summable_laurent_of_endpoint_summable [CompleteSpace K] [IsUltrametricDist K]
    (b : ℤ → K) (lo hi u : Kˣ)
    (hlo : Summable (fun n : ℤ => b n * (lo : K) ^ n))
    (hhi : Summable (fun n : ℤ => b n * (hi : K) ^ n))
    (hlu : ‖(lo : K)‖ ≤ ‖(u : K)‖)
    (huh : ‖(u : K)‖ ≤ ‖(hi : K)‖) :
    Summable (fun n : ℤ => b n * (u : K) ^ n) := by
  have hloPos : 0 < ‖(lo : K)‖ := norm_pos_iff.mpr lo.ne_zero
  have huPos : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hbound : ∀ n : ℤ, ‖b n * (u : K) ^ n‖ ≤
      ‖b n * (lo : K) ^ n‖ + ‖b n * (hi : K) ^ n‖ := by
    intro n
    by_cases hn : 0 ≤ n
    · have hp : ‖(u : K)‖ ^ n ≤ ‖(hi : K)‖ ^ n :=
        zpow_le_zpow_left₀ hn (norm_nonneg _) huh
      have hterm : ‖b n * (u : K) ^ n‖ ≤ ‖b n * (hi : K) ^ n‖ := by
        simp only [norm_mul, norm_zpow]
        exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      exact hterm.trans (le_add_of_nonneg_left (norm_nonneg _))
    · have hn' : 0 ≤ -n := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hn))
      have hp : ‖(lo : K)‖ ^ (-n) ≤ ‖(u : K)‖ ^ (-n) :=
        zpow_le_zpow_left₀ hn' (norm_nonneg _) hlu
      have hinv : (‖(u : K)‖ ^ (-n))⁻¹ ≤ (‖(lo : K)‖ ^ (-n))⁻¹ :=
        (inv_le_inv₀ (zpow_pos huPos (-n)) (zpow_pos hloPos (-n))).2 hp
      have hp' : ‖(u : K)‖ ^ n ≤ ‖(lo : K)‖ ^ n := by
        simpa only [← zpow_neg, neg_neg] using hinv
      have hterm : ‖b n * (u : K) ^ n‖ ≤ ‖b n * (lo : K) ^ n‖ := by
        simp only [norm_mul, norm_zpow]
        exact mul_le_mul_of_nonneg_left hp' (norm_nonneg _)
      exact hterm.trans (le_add_of_nonneg_right (norm_nonneg _))
  have hLo : Tendsto (fun n : ℤ => ‖b n * (lo : K) ^ n‖) cofinite (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hlo.tendsto_cofinite_zero.norm
  have hHi : Tendsto (fun n : ℤ => ‖b n * (hi : K) ^ n‖) cofinite (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hhi.tendsto_cofinite_zero.norm
  have hsumNorm : Tendsto
      (fun n : ℤ => ‖b n * (lo : K) ^ n‖ + ‖b n * (hi : K) ^ n‖)
      cofinite (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hLo.add hHi
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  exact squeeze_zero_norm hbound hsumNorm

/-- The q-power closed annuli cover every nonzero point. This uses only positive
real radii, without any discreteness condition on the value group of K. -/
theorem exists_q_closed_annulus (t : TateParameter K) (u : Kˣ) :
    ∃ m : ℤ, InQClosedAnnulus t m u := by
  have huPos : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hbase : 1 < ‖(t.q : K)‖⁻¹ := (one_lt_inv₀ t.norm_q_pos).2 t.norm_lt_one
  obtain ⟨n, hnlo, hnhi⟩ := exists_mem_Ico_zpow huPos hbase
  have hlo : ‖(t.q : K)‖ ^ (-n) ≤ ‖(u : K)‖ := by
    simpa only [inv_zpow'] using hnlo
  have hhi : ‖(u : K)‖ < ‖(t.q : K)‖ ^ (-n - 1) := by
    simpa only [inv_zpow', neg_add, sub_eq_add_neg] using hnhi
  refine ⟨-n, ?_, hhi.le⟩
  have hexp : -n ≤ -n + 1 := le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1)
  exact (zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le hexp).trans hlo

/-- Instantiate the endpoint test at the two q-power boundary points. -/
theorem summable_on_q_closed_annulus [CompleteSpace K] [IsUltrametricDist K]
    (t : TateParameter K) (m : ℤ) (b : ℤ → K)
    (hlo : Summable (fun n : ℤ => b n * ((t.q ^ (m + 1) : Kˣ) : K) ^ n))
    (hhi : Summable (fun n : ℤ => b n * ((t.q ^ (m - 1) : Kˣ) : K) ^ n))
    (u : Kˣ) (hu : InQClosedAnnulus t m u) :
    Summable (fun n : ℤ => b n * (u : K) ^ n) := by
  apply summable_laurent_of_endpoint_summable b (t.q ^ (m + 1))
    (t.q ^ (m - 1)) u hlo hhi
  · simpa only [Units.val_zpow_eq_zpow_val, norm_zpow] using hu.1
  · simpa only [Units.val_zpow_eq_zpow_val, norm_zpow] using hu.2

/-- The central q-power lies in its indexed annulus. -/
theorem qpow_mem_q_closed_annulus (t : TateParameter K) (m : ℤ) :
    InQClosedAnnulus t m (t.q ^ m) := by
  simp only [InQClosedAnnulus, Units.val_zpow_eq_zpow_val, norm_zpow]
  constructor
  · exact zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le
      (le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1))
  · exact zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le
      (sub_le_self m (by decide : (0 : ℤ) ≤ 1))

/-- The same q-power lies on the outer boundary of the next annulus. -/
theorem qpow_mem_next_q_closed_annulus (t : TateParameter K) (m : ℤ) :
    InQClosedAnnulus t (m + 1) (t.q ^ m) := by
  simp only [InQClosedAnnulus, Units.val_zpow_eq_zpow_val, norm_zpow, add_sub_cancel_right]
  constructor
  · have h1 : m ≤ m + 1 := le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1)
    have h2 : m + 1 ≤ m + 1 + 1 := le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1)
    exact zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le (h1.trans h2)
  · exact le_rfl

end CoreAnnularConvergence

#print axioms CoreAnnularConvergence.summable_laurent_of_endpoint_summable
#print axioms CoreAnnularConvergence.exists_q_closed_annulus
#print axioms CoreAnnularConvergence.summable_on_q_closed_annulus
#print axioms CoreAnnularConvergence.qpow_mem_q_closed_annulus
#print axioms CoreAnnularConvergence.qpow_mem_next_q_closed_annulus