import Boundary.ProjectiveComparison
import TateCurvesTheta.Kummer.ThetaGermCore

/-! Actual theta germs under the generating q-translation. The power series and
theta function are the upstream coefficientwise analytic definitions, not a
postulated family satisfying the desired functional equation. -/
set_option autoImplicit false
noncomputable section

namespace CoreThetaGermTransport
open PowerSeries TateCurvesTheta TateCurvesTheta.TateParameter Filter Topology

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K)

theorem summable_germ_coefficient (u : Kˣ) (k : ℕ) :
    Summable (fun n : ℤ => t.thetaTerm u n * (binomCoeff n k : K)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  have hnorm : Tendsto (fun n => ‖t.thetaTerm u n‖) cofinite (𝓝 0) := by
    simpa using (t.thetaTerm_summable u).tendsto_cofinite_zero.norm
  apply squeeze_zero_norm (fun n => ?_) hnorm
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_binomCoeff_le_one n k)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem thetaTerm_q_shift (u : Kˣ) (n : ℤ) :
    ((t.q * u : Kˣ) : K) * t.thetaTerm (t.q * u) n = t.thetaTerm u (n + 1) := by
  have he : thetaExp (n + 1) = thetaExp n + n + 1 := by
    rw [thetaExp_add, thetaExp_one]
    ring
  simp only [thetaTerm, Units.val_mul, mul_zpow, he]
  rw [zpow_add₀ t.q.ne_zero, zpow_add₀ t.q.ne_zero, zpow_one,
    zpow_add_one₀ u.ne_zero]
  ring

/-- The generating translation law is an equality of the actual entire formal
germs. It retains the nonconstant factor (1+X) and the constant q*u. -/
theorem thetaGerm_q_mul (u : Kˣ) :
    C (((t.q * u : Kˣ) : K)) * ((1 + X) * t.thetaGerm (t.q * u)) =
      t.thetaGerm u := by
  ext k
  cases k with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff_apply, map_mul, map_add, map_one,
      constantCoeff_X, constantCoeff_C, add_zero, one_mul, constantCoeff_thetaGerm]
    simpa only [thetaExp_one, zpow_one, Units.val_mul] using
      (t.theta_zpow_smul_eq u 1).symm
  | succ k =>
    rw [coeff_C_mul, add_mul, one_mul, map_add, coeff_succ_X_mul,
      coeff_thetaGerm, coeff_thetaGerm, coeff_thetaGerm,
      ← (summable_germ_coefficient t (t.q * u) (k + 1)).tsum_add
        (summable_germ_coefficient t (t.q * u) k), ← tsum_mul_left]
    rw [← Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
      (fun n => t.thetaTerm u n * (binomCoeff n (k + 1) : K))]
    apply tsum_congr
    intro n
    simp only [Equiv.coe_addRight, binomCoeff_add_one_succ, Int.cast_add]
    rw [← thetaTerm_q_shift t u n]
    ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Nonvanishing is transported by the actual q-functional equation. -/
theorem theta_q_mul_ne_zero (u : Kˣ) (hu : t.theta u ≠ 0) :
    t.theta (t.q * u) ≠ 0 := by
  rw [t.theta_q_smul]
  exact mul_ne_zero (inv_ne_zero (mul_ne_zero t.q.ne_zero u.ne_zero)) hu

/-- The genuine binomial coordinate unit over K. -/
def coordinateUnit : (K⟦X⟧)ˣ :=
  Units.map (PowerSeries.map (Int.castRingHom K)).toMonoidHom onePlusX

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem coe_coordinateUnit : (coordinateUnit (K := K) : K⟦X⟧) = 1 + X := by
  simp [coordinateUnit]

def constantUnit (a : Kˣ) : (K⟦X⟧)ˣ :=
  Units.map (C : K →+* K⟦X⟧).toMonoidHom a

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem coe_constantUnit (a : Kˣ) : (constantUnit a : K⟦X⟧) = C (a : K) := rfl

/-- Equality of actual unit germs; the correction is not postulated trivial. -/
theorem thetaGermUnit_q_mul (u : Kˣ) (hu : t.theta u ≠ 0) :
    t.thetaGermUnit (t.q * u) (theta_q_mul_ne_zero t u hu) =
      (constantUnit (t.q * u) * coordinateUnit)⁻¹ * t.thetaGermUnit u hu := by
  apply eq_inv_mul_iff_mul_eq.mpr
  apply Units.ext
  simpa only [Units.val_mul, coe_constantUnit, coe_coordinateUnit,
    coe_thetaGermUnit, mul_assoc] using thetaGerm_q_mul t u

theorem map_thetaGermUnit_q_mul {H : Type*} [CommGroup H]
    (φ : (K⟦X⟧)ˣ →* H) (u : Kˣ) (hu : t.theta u ≠ 0) :
    φ (t.thetaGermUnit (t.q * u) (theta_q_mul_ne_zero t u hu)) =
      (φ (constantUnit (t.q * u)) * φ coordinateUnit)⁻¹ * φ (t.thetaGermUnit u hu) := by
  rw [thetaGermUnit_q_mul, map_mul, map_inv, map_mul]

def toFieldUnits (F : Type*) [Field F] [Algebra K⟦X⟧ F] : (K⟦X⟧)ˣ →* Fˣ :=
  Units.map (algebraMap K⟦X⟧ F : K⟦X⟧ →* F)

open KummerTheory IsLocalRing KummerTheory.Decomposition

theorem kummer_thetaGermUnit_q_mul {F Ω : Type*} [Field F] [Field Ω]
    [Algebra K⟦X⟧ F] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (n : ℕ) [HasKummerRoots n F Ω] (u : Kˣ) (hu : t.theta u ≠ 0) :
    kummer n F Ω (toFieldUnits (K := K) F (t.thetaGermUnit (t.q * u) (theta_q_mul_ne_zero t u hu))) =
      (kummer n F Ω (toFieldUnits (K := K) F (constantUnit (t.q * u))) *
        kummer n F Ω (toFieldUnits (K := K) F coordinateUnit))⁻¹ *
          kummer n F Ω (toFieldUnits (K := K) F (t.thetaGermUnit u hu)) :=
  map_thetaGermUnit_q_mul t ((kummer n F Ω).comp (toFieldUnits (K := K) F)) u hu

section Reduction
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra K F] [Algebra K⟦X⟧ F]
  [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ A)
  [Algebra K (ResidueField A)]
  (hkres : ∀ c : K, residue A ⟨algebraMap K Ω c, hk c⟩ =
    algebraMap K (ResidueField A) c)
  [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K (ResidueField A)]
  (n : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]

/-- The actual restriction and coefficient reduction, composed with the map
from power-series units to function-field units and the genuine Kummer map. -/
def reducedGermHom : letI := muAction F A hk hkres n
    (K⟦X⟧)ˣ →* ContH1 (A.decompositionSubgroup F) (Mu n (ResidueField A)) :=
  let _ := muAction F A hk hkres n
  ((ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
    (reduceMu A n hn) continuous_of_discreteTopology (reduceMu_smul F A hk hkres n hn)).comp
      (kummer n F Ω)).comp (toFieldUnits (K := K) F)

variable (hA : ∀ s : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F s) ∈ A)
  (hX : residue A ⟨_, hA X⟩ = 0) [HasKummerRoots n K (ResidueField A)]

include hA hX in
omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The nonconstant coordinate factor vanishes only after the actual reduced
restriction at X=0, by specialization to the value 1. -/
theorem reduced_coordinate_eq_one :
    reducedGermHom (F := F) A hk hkres n hn (coordinateUnit (K := K)) = 1 := by
  let _ := muAction F A hk hkres n
  let f := toFieldUnits (K := K) F (coordinateUnit (K := K))
  have hf : algebraMap F Ω (f : F) ∈ A := hA (coordinateUnit (K := K) : K⟦X⟧)
  have hf' : algebraMap F Ω ((f⁻¹ : Fˣ) : F) ∈ A :=
    hA (((coordinateUnit (K := K))⁻¹ : (K⟦X⟧)ˣ) : K⟦X⟧)
  have hfa : residue A ⟨_, hf⟩ = algebraMap K (ResidueField A) (1 : Kˣ) := by
    have he : (⟨_, hf⟩ : A) = 1 + ⟨_, hA X⟩ := by
      apply Subtype.ext
      change algebraMap F Ω (algebraMap K⟦X⟧ F (coordinateUnit (K := K) : K⟦X⟧)) =
        (1 : Ω) + algebraMap F Ω (algebraMap K⟦X⟧ F X)
      simp only [coe_coordinateUnit, map_add, map_one]
    rw [he, map_add, map_one, hX, add_zero]
    simp
  have h := decomposition_kummer F A hk hkres n hn f 1 hf hf' hfa
  change (ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
    (reduceMu A n hn) continuous_of_discreteTopology (reduceMu_smul F A hk hkres n hn))
      ((kummer n F Ω) f) = 1
  simpa only [map_one] using h

variable (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c)

include hA hCF in
omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The remaining constant factor specializes to its actual arithmetic Kummer
class; it is not declared trivial. -/
theorem reduced_constant (a : Kˣ) :
    letI := muAction F A hk hkres n
    reducedGermHom (F := F) A hk hkres n hn (constantUnit a) =
      ContH1.map (decompositionMap F A hk hkres) (continuous_decompositionMap F A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl) (kummer n K (ResidueField A) a) := by
  let f := toFieldUnits (K := K) F (constantUnit a)
  have hf : algebraMap F Ω (f : F) ∈ A := hA (constantUnit a : K⟦X⟧)
  have hf' : algebraMap F Ω ((f⁻¹ : Fˣ) : F) ∈ A :=
    hA (((constantUnit a)⁻¹ : (K⟦X⟧)ˣ) : K⟦X⟧)
  have hfa : residue A ⟨_, hf⟩ = algebraMap K (ResidueField A) a := by
    have he : (⟨_, hf⟩ : A) = ⟨_, hk a⟩ := by
      apply Subtype.ext
      change algebraMap F Ω (algebraMap K⟦X⟧ F (C (a : K))) = algebraMap K Ω a
      rw [hCF, IsScalarTower.algebraMap_apply K F Ω]
    rw [he, hkres]
  exact decomposition_kummer F A hk hkres n hn f a hf hf' hfa

include hA hX hCF in
/-- A source-derived comparison on the same decomposition group. Only the
coordinate-unit class is removed, via specialization; q*u remains explicit. -/
theorem reduced_thetaGermUnit_q_mul (u : Kˣ) (hu : t.theta u ≠ 0) :
    letI := muAction F A hk hkres n
    reducedGermHom (F := F) A hk hkres n hn
        (t.thetaGermUnit (t.q * u) (theta_q_mul_ne_zero t u hu)) =
      (ContH1.map (decompositionMap F A hk hkres) (continuous_decompositionMap F A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl)
          (kummer n K (ResidueField A) (t.q * u)))⁻¹ *
            reducedGermHom (F := F) A hk hkres n hn (t.thetaGermUnit u hu) := by
  let _ := muAction F A hk hkres n
  have h := map_thetaGermUnit_q_mul t (reducedGermHom (F := F) A hk hkres n hn) u hu
  rw [reduced_coordinate_eq_one A hk hkres n hn hA hX,
    reduced_constant A hk hkres n hn hA hCF, mul_one] at h
  exact h
end Reduction

open CoreDiscreteKummer CoreAnchoredComparison
open scoped WithZero Pointwise

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The actual constant correction changes arithmetic exponents by -w(q)-w(u).
No identification of the arithmetic valuation with the X-adic one is made. -/
theorem exponent_theta_q_mul (v : Valuation K ℤᵐ⁰) (u : Kˣ) (hu : t.theta u ≠ 0) :
    exponent v (t.theta (t.q * u)) =
      exponent v (t.theta u) - exponent v (t.q : K) - exponent v (u : K) := by
  rw [t.theta_q_smul]
  simp only [exponent, map_mul, map_inv₀]
  rw [WithZero.log_mul (inv_ne_zero (mul_ne_zero
    (v.ne_zero_iff.mpr t.q.ne_zero) (v.ne_zero_iff.mpr u.ne_zero)))
      (v.ne_zero_iff.mpr hu), WithZero.log_inv,
    WithZero.log_mul (v.ne_zero_iff.mpr t.q.ne_zero) (v.ne_zero_iff.mpr u.ne_zero)]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The generating geometric translation preserves the arithmetic principal
lattice exactly when its explicit automorphy factor has zero exponent. -/
theorem principal_eq_iff_zero_automorphy_exponent (v : Valuation K ℤᵐ⁰)
    (u : Kˣ) (hu : t.theta u ≠ 0) :
    t.theta (t.q * u) • integerRegion v = t.theta u • integerRegion v ↔
      exponent v (t.q : K) + exponent v (u : K) = 0 := by
  constructor
  · intro h
    have he := exponent_eq_of_principal_eq v
      (Units.mk0 _ (theta_q_mul_ne_zero t u hu)) (Units.mk0 _ hu) h
    have hf := exponent_theta_q_mul t v u hu
    change exponent v (t.theta (t.q * u)) = exponent v (t.theta u) at he
    omega
  · intro h
    apply principal_eq_of_exponent_eq v (theta_q_mul_ne_zero t u hu) hu
    have hf := exponent_theta_q_mul t v u hu
    omega

end CoreThetaGermTransport

#print axioms CoreThetaGermTransport.summable_germ_coefficient
#print axioms CoreThetaGermTransport.thetaTerm_q_shift
#print axioms CoreThetaGermTransport.thetaGerm_q_mul
#print axioms CoreThetaGermTransport.theta_q_mul_ne_zero
#print axioms CoreThetaGermTransport.coordinateUnit
#print axioms CoreThetaGermTransport.coe_coordinateUnit
#print axioms CoreThetaGermTransport.constantUnit
#print axioms CoreThetaGermTransport.coe_constantUnit
#print axioms CoreThetaGermTransport.thetaGermUnit_q_mul
#print axioms CoreThetaGermTransport.map_thetaGermUnit_q_mul
#print axioms CoreThetaGermTransport.toFieldUnits
#print axioms CoreThetaGermTransport.kummer_thetaGermUnit_q_mul
#print axioms CoreThetaGermTransport.reducedGermHom
#print axioms CoreThetaGermTransport.reduced_coordinate_eq_one
#print axioms CoreThetaGermTransport.reduced_constant
#print axioms CoreThetaGermTransport.reduced_thetaGermUnit_q_mul
#print axioms CoreThetaGermTransport.exponent_theta_q_mul
#print axioms CoreThetaGermTransport.principal_eq_iff_zero_automorphy_exponent
