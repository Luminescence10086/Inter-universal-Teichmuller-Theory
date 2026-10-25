import Boundary.SphereNonvanishing
import Boundary.AnnularOverlap
import Boundary.TwistedThetaCurvature

/-! Synchronize independently supplied constant deck factors on a q-annular atlas.
The factors are compared at an actual shared point where the global Laurent
function is nonzero. Nonvanishing on each shared sphere follows from coefficient
uniqueness; it is not an extra premise. Coordinates and function frames are fixed
as in annular descent. No original tempered realization or primitive deck
identification is constructed by these theorems. -/
set_option autoImplicit false
noncomputable section

namespace CoreLocalDeckSynchronization
open TateCurvesTheta CoreAnnularConvergence CoreAnnularThetaDescent
open CoreGlobalThetaRigidity

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K) (B : ℤ → ℤ → K)
  (hinner : ∀ m : ℤ,
    Summable (fun n : ℤ => B m n * ((t.q ^ (m + 1) : Kˣ) : K) ^ n))
  (houter : ∀ m : ℤ,
    Summable (fun n : ℤ => B m n * ((t.q ^ (m - 1) : Kˣ) : K) ^ n))
  (hoverlap : ∀ (m : ℤ) (v : Kˣ), ‖(v : K)‖ = 1 →
    (∑' n : ℤ, B m n * (((t.q ^ m) * v : Kˣ) : K) ^ n) =
      ∑' n : ℤ, B (m + 1) n * (((t.q ^ m) * v : Kˣ) : K) ^ n)
  (hnonzero : ∃ (m : ℤ) (u : Kˣ),
    InQClosedAnnulus t m u ∧ laurentValue (B m) u ≠ 0)

include hinner houter hoverlap hnonzero

/-- One nonzero local value makes the glued coefficient family nonzero.
This step does not use a deck law or a nonzero constant coefficient. -/
theorem global_family_ne_zero : B 0 ≠ 0 := by
  obtain ⟨m, u, _hu, hne⟩ := hnonzero
  rw [coefficient_families_eq t B hinner houter hoverlap m] at hne
  exact CoreSphereNonvanishing.b_ne_zero_of_value (B 0) u hne

/-- Each neighboring pair has a shared point with nonzero Laurent value. -/
theorem shared_nonzero_point (m : ℤ) :
    ∃ u : Kˣ, InQClosedAnnulus t m u ∧ InQClosedAnnulus t (m + 1) u ∧
      laurentValue (B 0) u ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := CoreSphereNonvanishing.exists_nonzero_on_sphere
    t (B 0) (t.q ^ m) (global_summable t B hinner houter hoverlap (t.q ^ m))
    (global_family_ne_zero t B hinner houter hoverlap hnonzero)
  exact ⟨t.q ^ m * v, CoreAnnularOverlap.qpow_mul_mem_annulus t m v hv,
    CoreAnnularOverlap.qpow_mul_mem_next_annulus t m v hv, hne⟩

variable (α : ℤ → Kˣ)
  (hdeck : ∀ (m : ℤ) (u : Kˣ), InQClosedAnnulus t m u →
    (∑' n : ℤ, B (m + 1) n * ((t.q : K) * (u : K)) ^ n) =
      (α m : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, B m n * (u : K) ^ n))

include hdeck

/-- Compare the two actual local transitions at a shared nonzero point. -/
theorem constants_eq_succ (m : ℤ) : α (m + 1) = α m := by
  obtain ⟨u, hu, hunext, hne⟩ :=
    shared_nonzero_point t B hinner houter hoverlap hnonzero m
  have heq := coefficient_families_eq t B hinner houter hoverlap
  have hleft := hdeck m u hu
  have hright := hdeck (m + 1) u hunext
  simp only [heq (m + 1), heq m] at hleft
  simp only [heq ((m + 1) + 1), heq (m + 1)] at hright
  have hC : ((t.q : K) * (u : K))⁻¹ *
      (∑' n : ℤ, B 0 n * (u : K) ^ n) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (mul_ne_zero t.q.ne_zero u.ne_zero)) hne
  apply Units.ext
  apply mul_right_cancel₀ hC
  simpa only [mul_assoc] using hright.symm.trans hleft

/-- The common deck constant is forced by all neighboring comparisons. -/
theorem constants_eq_zero (m : ℤ) : α m = α 0 :=
  CoreSphereCoefficientDescent.family_eq_zero_of_eq_succ α
    (constants_eq_succ t B hinner houter hoverlap hnonzero α hdeck) m

/-- Both the global function and its common deck factor are derived from local data. -/
theorem global_twisted_law (u : Kˣ) :
    (∑' n : ℤ, B 0 n * ((t.q : K) * (u : K)) ^ n) =
      (α 0 : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, B 0 n * (u : K) ^ n) := by
  obtain ⟨m, hm⟩ := exists_q_closed_annulus t u
  have heq := coefficient_families_eq t B hinner houter hoverlap
  simpa only [heq (m + 1), heq m,
    constants_eq_zero t B hinner houter hoverlap hnonzero α hdeck m] using hdeck m u hm

/-- The common constant is an output; no cross-annulus scalar equality is assumed. -/
theorem exists_common_twist :
    ∃ a : Kˣ, (∀ m : ℤ, α m = a) ∧ ∀ u : Kˣ,
      (∑' n : ℤ, B 0 n * ((t.q : K) * (u : K)) ^ n) =
        (a : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, B 0 n * (u : K) ^ n) := by
  exact ⟨α 0, constants_eq_zero t B hinner houter hoverlap hnonzero α hdeck,
    global_twisted_law t B hinner houter hoverlap hnonzero α hdeck⟩

/-- The coefficient curvature recovers q even when each annulus initially has
its own independently supplied nonzero constant deck factor. -/
theorem locally_twisted_curvature_eq_q (n : ℤ) :
    (B 0 (n + 2) * B 0 n) / (B 0 (n + 1) ^ 2) = (t.q : K) := by
  apply CoreTwistedThetaCurvature.annular_curvature_eq_q t (α 0) B
    hinner houter hoverlap _ hnonzero n
  intro m u hu
  simpa only [constants_eq_zero t B hinner houter hoverlap hnonzero α hdeck m]
    using hdeck m u hu

end CoreLocalDeckSynchronization

#print axioms CoreLocalDeckSynchronization.global_family_ne_zero
#print axioms CoreLocalDeckSynchronization.shared_nonzero_point
#print axioms CoreLocalDeckSynchronization.constants_eq_succ
#print axioms CoreLocalDeckSynchronization.constants_eq_zero
#print axioms CoreLocalDeckSynchronization.global_twisted_law
#print axioms CoreLocalDeckSynchronization.exists_common_twist
#print axioms CoreLocalDeckSynchronization.locally_twisted_curvature_eq_q
