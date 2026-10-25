import Boundary.AnnularThetaDescent

/-! A constant twist in the theta deck law is removed by reweighting the
Laurent coefficients. The second multiplicative difference of coefficients
retains q while eliminating the constant twist and the common section scalar.
This module concerns one fixed Tate coordinate and a primitive q-translation;
it does not construct an original tempered theta source. -/
set_option autoImplicit false
noncomputable section

namespace CoreTwistedThetaCurvature

open TateCurvesTheta TateCurvesTheta.TateParameter CoreGlobalThetaRigidity

variable {K : Type*} [NormedField K]

/-- Coefficient reweighting corresponding to the coordinate change u ↦ α*u. -/
def weightedCoeff (α : Kˣ) (b : ℤ → K) (n : ℤ) : K := (α : K) ^ n * b n

private theorem weighted_sum_eq (α : Kˣ) (b : ℤ → K) (u : Kˣ) :
    (∑' n : ℤ, weightedCoeff α b n * (u : K) ^ n) =
      ∑' n : ℤ, b n * ((α * u : Kˣ) : K) ^ n := by
  refine tsum_congr fun n => ?_
  simp only [weightedCoeff, Units.val_mul, mul_zpow]
  ring

/-- Reweighting preserves global convergence, by evaluating the original family
at the actual nonzero point α*u. -/
theorem weighted_summable (α : Kˣ) (b : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n)) (u : Kˣ) :
    Summable (fun n : ℤ => weightedCoeff α b n * (u : K) ^ n) := by
  refine (hsum (α * u)).congr fun n => ?_
  simp only [weightedCoeff, Units.val_mul, mul_zpow]
  ring

/-- The unknown nonzero constant in the deck law disappears after reweighting. -/
theorem weighted_automorphy (t : TateParameter K) (α : Kˣ) (b : ℤ → K)
    (htwist : ∀ u : Kˣ,
      (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))
    (u : Kˣ) :
    (∑' n : ℤ, weightedCoeff α b n * ((t.q : K) * (u : K)) ^ n) =
      ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, weightedCoeff α b n * (u : K) ^ n) := by
  have hfac : (α : K) * ((t.q : K) * ((α * u : Kˣ) : K))⁻¹ =
      ((t.q : K) * (u : K))⁻¹ := by
    simp only [Units.val_mul, mul_inv]
    calc
      (α : K) * ((t.q : K)⁻¹ * ((α : K)⁻¹ * (u : K)⁻¹)) =
          ((α : K) * (α : K)⁻¹) * ((t.q : K)⁻¹ * (u : K)⁻¹) := by ring
      _ = (t.q : K)⁻¹ * (u : K)⁻¹ := by rw [mul_inv_cancel₀ α.ne_zero, one_mul]
  change (∑' n : ℤ, weightedCoeff α b n * ((t.q * u : Kˣ) : K) ^ n) = _
  rw [weighted_sum_eq, weighted_sum_eq, mul_left_comm α t.q u]
  change (∑' n : ℤ, b n * ((t.q : K) * ((α * u : Kˣ) : K)) ^ n) = _
  rw [htwist (α * u), hfac]

variable [CompleteSpace K] [IsUltrametricDist K]

/-- The twisted deck law determines every coefficient, including its linear
exponent twist α^(-n), from b 0. -/
theorem twisted_coeff_eq (t : TateParameter K) (α : Kˣ) (b : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n))
    (htwist : ∀ u : Kˣ,
      (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))
    (n : ℤ) :
    b n = b 0 * (α : K) ^ (-n) * (t.q : K) ^ thetaExp n := by
  have h := laurent_coeff_eq_theta_coeff t (weightedCoeff α b)
    (weighted_summable α b hsum) (weighted_automorphy t α b htwist) n
  simp only [weightedCoeff, zpow_zero, one_mul] at h
  calc
    b n = (α : K) ^ (-n) * ((α : K) ^ n * b n) := by
      rw [← mul_assoc, ← zpow_add₀ α.ne_zero, neg_add_cancel, zpow_zero, one_mul]
    _ = (α : K) ^ (-n) * (b 0 * (t.q : K) ^ thetaExp n) := by rw [h]
    _ = b 0 * (α : K) ^ (-n) * (t.q : K) ^ thetaExp n := by ring

/-- A nonzero section coefficient at zero forces all coefficients to be nonzero. -/
theorem twisted_coeff_ne_zero (t : TateParameter K) (α : Kˣ) (b : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n))
    (htwist : ∀ u : Kˣ,
      (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))
    (hb0 : b 0 ≠ 0) (n : ℤ) : b n ≠ 0 := by
  rw [twisted_coeff_eq t α b hsum htwist n]
  exact mul_ne_zero (mul_ne_zero hb0 (zpow_ne_zero _ α.ne_zero)) (zpow_ne_zero _ t.q.ne_zero)

private theorem twisted_coeff_recurrence (t : TateParameter K) (α : Kˣ) (b : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n))
    (htwist : ∀ u : Kˣ,
      (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))
    (n : ℤ) : b (n + 1) = (α : K)⁻¹ * (t.q : K) ^ (n + 1) * b n := by
  have he : thetaExp (n + 1) = thetaExp n + (n + 1) := by
    rw [thetaExp_add, thetaExp_one]
    ring
  have hn : -(n + 1) = -n + (-1 : ℤ) := by omega
  rw [twisted_coeff_eq t α b hsum htwist (n + 1),
    twisted_coeff_eq t α b hsum htwist n, he, hn,
    zpow_add₀ α.ne_zero (-n) (-1), zpow_neg_one,
    zpow_add₀ t.q.ne_zero (thetaExp n) (n + 1)]
  ring

/-- The second multiplicative coefficient difference recovers the Tate parameter;
the constant deck twist α and the common scalar b 0 both cancel. -/
theorem coefficient_curvature_eq_q (t : TateParameter K) (α : Kˣ) (b : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable (fun n : ℤ => b n * (u : K) ^ n))
    (htwist : ∀ u : Kˣ,
      (∑' n : ℤ, b n * ((t.q : K) * (u : K)) ^ n) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' n : ℤ, b n * (u : K) ^ n))
    (hb0 : b 0 ≠ 0) (n : ℤ) :
    (b (n + 2) * b n) / (b (n + 1) ^ 2) = (t.q : K) := by
  have hn := twisted_coeff_recurrence t α b hsum htwist n
  have hn1 := twisted_coeff_recurrence t α b hsum htwist (n + 1)
  have hnext : b (n + 2) =
      (t.q : K) * ((α : K)⁻¹ * (t.q : K) ^ (n + 1)) * b (n + 1) := by
    calc
      b (n + 2) = b ((n + 1) + 1) := by
        congr 1
        omega
      _ = (α : K)⁻¹ * (t.q : K) ^ ((n + 1) + 1) * b (n + 1) := hn1
      _ = (t.q : K) * ((α : K)⁻¹ * (t.q : K) ^ (n + 1)) * b (n + 1) := by
        rw [zpow_add_one₀ t.q.ne_zero]
        ring
  have hid : b (n + 2) * b n = (t.q : K) * b (n + 1) ^ 2 := by
    calc
      b (n + 2) * b n =
          ((t.q : K) * ((α : K)⁻¹ * (t.q : K) ^ (n + 1)) * b (n + 1)) * b n := by
            rw [hnext]
      _ = (t.q : K) * b (n + 1) * ((α : K)⁻¹ * (t.q : K) ^ (n + 1) * b n) := by ring
      _ = (t.q : K) * b (n + 1) * b (n + 1) := by rw [← hn]
      _ = (t.q : K) * b (n + 1) ^ 2 := by ring
  rw [hid]
  exact mul_div_cancel_right₀ (t.q : K)
    (pow_ne_zero 2 (twisted_coeff_ne_zero t α b hsum htwist hb0 (n + 1)))

/-- Local endpoint convergence, overlap agreement, and a locally stated deck
transition with an unknown nonzero constant suffice for the curvature readout.
Neither a global coefficient family nor its global convergence is assumed.
All charts use the same coordinate and function frame as in annular descent. -/
theorem annular_curvature_eq_q (t : TateParameter K) (α : Kˣ) (B : ℤ → ℤ → K)
    (hinner : ∀ m : ℤ,
      Summable (fun j : ℤ => B m j * ((t.q ^ (m + 1) : Kˣ) : K) ^ j))
    (houter : ∀ m : ℤ,
      Summable (fun j : ℤ => B m j * ((t.q ^ (m - 1) : Kˣ) : K) ^ j))
    (hoverlap : ∀ (m : ℤ) (v : Kˣ), ‖(v : K)‖ = 1 →
      (∑' j : ℤ, B m j * (((t.q ^ m) * v : Kˣ) : K) ^ j) =
        ∑' j : ℤ, B (m + 1) j * (((t.q ^ m) * v : Kˣ) : K) ^ j)
    (hlocaldeck : ∀ (m : ℤ) (u : Kˣ), CoreAnnularConvergence.InQClosedAnnulus t m u →
      (∑' j : ℤ, B (m + 1) j * ((t.q : K) * (u : K)) ^ j) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' j : ℤ, B m j * (u : K) ^ j))
    (hnonzero : ∃ (m : ℤ) (u : Kˣ),
      CoreAnnularConvergence.InQClosedAnnulus t m u ∧ laurentValue (B m) u ≠ 0)
    (n : ℤ) : (B 0 (n + 2) * B 0 n) / (B 0 (n + 1) ^ 2) = (t.q : K) := by
  have heq := CoreAnnularThetaDescent.coefficient_families_eq t B hinner houter hoverlap
  have hsum := CoreAnnularThetaDescent.global_summable t B hinner houter hoverlap
  have htwist : ∀ u : Kˣ,
      (∑' j : ℤ, B 0 j * ((t.q : K) * (u : K)) ^ j) =
        (α : K) * ((t.q : K) * (u : K))⁻¹ * (∑' j : ℤ, B 0 j * (u : K) ^ j) := by
    intro u
    obtain ⟨m, hm⟩ := CoreAnnularConvergence.exists_q_closed_annulus t u
    simpa only [heq (m + 1), heq m] using hlocaldeck m u hm
  have hb0 : B 0 0 ≠ 0 := by
    intro hzero
    obtain ⟨m, u, _hu, hne⟩ := hnonzero
    have hvalue : laurentValue (B m) u = 0 := by
      rw [heq m, laurentValue]
      have hz (j : ℤ) : B 0 j * (u : K) ^ j = (0 : K) := by
        rw [twisted_coeff_eq t α (B 0) hsum htwist j, hzero]
        simp
      simpa only [tsum_zero] using tsum_congr hz
    exact hne hvalue
  exact coefficient_curvature_eq_q t α (B 0) hsum htwist hb0 n

end CoreTwistedThetaCurvature

#print axioms CoreTwistedThetaCurvature.weighted_summable
#print axioms CoreTwistedThetaCurvature.weighted_automorphy
#print axioms CoreTwistedThetaCurvature.twisted_coeff_eq
#print axioms CoreTwistedThetaCurvature.twisted_coeff_ne_zero
#print axioms CoreTwistedThetaCurvature.coefficient_curvature_eq_q
#print axioms CoreTwistedThetaCurvature.annular_curvature_eq_q
