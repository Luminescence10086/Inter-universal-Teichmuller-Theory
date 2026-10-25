import Boundary.AnnularConvergence
import Boundary.SphereCoefficientDescent
import Boundary.GlobalThetaRigidity

/-! Local Laurent expansions on overlapping q-annuli produce a global family.
Endpoint convergence and overlap agreement are local hypotheses. The common
family and its all-point convergence are conclusions. The deck equation is
derived from the explicitly stated local section transition; no construction
of the original tempered line bundle or its canonical frames is claimed here.
All coefficient families use the same multiplicative coordinate and function
frame. General sections in unrelated local line-bundle frames need their actual
overlap transition maps first; equality in this input is not inferred for them. -/
set_option autoImplicit false
noncomputable section

namespace CoreAnnularThetaDescent
open TateCurvesTheta CoreAnnularConvergence CoreGlobalThetaRigidity

variable {K : Type*} [NormedField K]

/-- Multiplication by the actual period sends each closed annulus to the next. -/
theorem q_mul_mem_annulus (t : TateParameter K) (m : ℤ) (u : Kˣ)
    (hu : InQClosedAnnulus t m u) : InQClosedAnnulus t (m + 1) (t.q * u) := by
  have hpow (n : ℤ) : ‖(t.q : K)‖ ^ (n + 1) =
      ‖(t.q : K)‖ * ‖(t.q : K)‖ ^ n := by
    rw [zpow_add_one₀ (ne_of_gt t.norm_q_pos)]
    ring
  change ‖(t.q : K)‖ ^ ((m + 1) + 1) ≤ ‖((t.q * u : Kˣ) : K)‖ ∧
    ‖((t.q * u : Kˣ) : K)‖ ≤ ‖(t.q : K)‖ ^ ((m + 1) - 1)
  rw [Units.val_mul, norm_mul]
  constructor
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hu.1 (norm_nonneg _)
  · calc
      ‖(t.q : K)‖ * ‖(u : K)‖ ≤ ‖(t.q : K)‖ * ‖(t.q : K)‖ ^ (m - 1) :=
        mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)
      _ = ‖(t.q : K)‖ ^ ((m + 1) - 1) := by
        rw [← hpow]
        congr 1
        omega

variable [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K) (B : ℤ → ℤ → K)
  (hinner : ∀ m : ℤ,
    Summable (fun n : ℤ => B m n * ((t.q ^ (m + 1) : Kˣ) : K) ^ n))
  (houter : ∀ m : ℤ,
    Summable (fun n : ℤ => B m n * ((t.q ^ (m - 1) : Kˣ) : K) ^ n))
  (hoverlap : ∀ (m : ℤ) (v : Kˣ), ‖(v : K)‖ = 1 →
    (∑' n : ℤ, B m n * (((t.q ^ m) * v : Kˣ) : K) ^ n) =
      ∑' n : ℤ, B (m + 1) n * (((t.q ^ m) * v : Kˣ) : K) ^ n)

include hinner houter hoverlap

/-- Local overlap agreement forces all actual coefficient families to coincide. -/
theorem coefficient_families_eq (m : ℤ) : B m = B 0 := by
  apply CoreSphereCoefficientDescent.coefficients_eq_of_adjacent_sphere_values
    t B (fun j => t.q ^ j) _ _ hoverlap m
  · intro j
    exact summable_on_q_closed_annulus t j (B j) (hinner j) (houter j)
      (t.q ^ j) (qpow_mem_q_closed_annulus t j)
  · intro j
    exact summable_on_q_closed_annulus t (j + 1) (B (j + 1))
      (hinner (j + 1)) (houter (j + 1)) (t.q ^ j)
      (qpow_mem_next_q_closed_annulus t j)

/-- Global convergence is obtained from endpoint convergence and the q-annulus cover. -/
theorem global_summable (u : Kˣ) :
    Summable (fun n : ℤ => B 0 n * (u : K) ^ n) := by
  obtain ⟨m, hm⟩ := exists_q_closed_annulus t u
  have h := summable_on_q_closed_annulus t m (B m) (hinner m) (houter m) u hm
  simpa only [coefficient_families_eq t B hinner houter hoverlap m] using h

variable
  (hdeck : ∀ (m : ℤ) (u : Kˣ), InQClosedAnnulus t m u →
    (∑' n : ℤ, B (m + 1) n * ((t.q : K) * (u : K)) ^ n) =
      ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, B m n * (u : K) ^ n))

include hdeck

/-- The global deck equation comes from a local section transition on the cover. -/
theorem global_deck (u : Kˣ) :
    (∑' n : ℤ, B 0 n * ((t.q : K) * (u : K)) ^ n) =
      ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, B 0 n * (u : K) ^ n) := by
  obtain ⟨m, hm⟩ := exists_q_closed_annulus t u
  simpa only [coefficient_families_eq t B hinner houter hoverlap (m + 1),
    coefficient_families_eq t B hinner houter hoverlap m] using hdeck m u hm

/-- A common global Laurent source is an output, not a field in the local input. -/
theorem exists_global_laurent_source :
    ∃ b : ℤ → K, (∀ m : ℤ, B m = b) ∧
      (∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n)) ∧
      (∀ u : Kˣ, (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n)) := by
  exact ⟨B 0, coefficient_families_eq t B hinner houter hoverlap,
    global_summable t B hinner houter hoverlap,
    global_deck t B hinner houter hoverlap hdeck⟩

/-- Every local expansion has the same theta scalar, derived from local input. -/
theorem all_local_series_common_scalar (m : ℤ) (u : Kˣ) :
    laurentValue (B m) u = B 0 0 * t.theta u := by
  rw [coefficient_families_eq t B hinner houter hoverlap m]
  exact laurentValue_eq_const_mul_theta t (B 0)
    (global_summable t B hinner houter hoverlap)
    (global_deck t B hinner houter hoverlap hdeck) u

/-- A nonzero local section gives a nonzero common scalar and retains the period.
The period and the monomial coordinate still belong to one fixed Tate realization. -/
theorem local_source_coefficients_recover_q
    (hnonzero : ∃ (m : ℤ) (u : Kˣ), InQClosedAnnulus t m u ∧ laurentValue (B m) u ≠ 0) :
    B 0 1 / B 0 0 = (t.q : K) := by
  obtain ⟨m, u, _hu, hne⟩ := hnonzero
  have hc : B 0 0 ≠ 0 := by
    intro hc
    rw [all_local_series_common_scalar t B hinner houter hoverlap hdeck m u,
      hc, zero_mul] at hne
    exact hne rfl
  exact laurent_coeff_one_div_zero t (B 0)
    (global_summable t B hinner houter hoverlap)
    (global_deck t B hinner houter hoverlap hdeck) hc

end CoreAnnularThetaDescent

#print axioms CoreAnnularThetaDescent.q_mul_mem_annulus
#print axioms CoreAnnularThetaDescent.coefficient_families_eq
#print axioms CoreAnnularThetaDescent.global_summable
#print axioms CoreAnnularThetaDescent.global_deck
#print axioms CoreAnnularThetaDescent.exists_global_laurent_source
#print axioms CoreAnnularThetaDescent.all_local_series_common_scalar
#print axioms CoreAnnularThetaDescent.local_source_coefficients_recover_q
