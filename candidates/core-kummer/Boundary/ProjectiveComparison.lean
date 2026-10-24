import Boundary.AnchoredComparison

/-! A shared Kummer coefficient power determines a projective valuation relation
even when the two anchors have different valuations. Unit corrections are kept
at every finite level. This does not construct an original IUT source transport.
The absolute scale is a separate obligation; a negative control records why. -/
set_option autoImplicit false

namespace CoreProjectiveComparison
open KummerTheory CoreDiscreteKummer CoreAnchoredComparison
open scoped WithZero Pointwise

theorem dvd_cross_determinant (N A B e f u : ℤ)
    (hvalue : N ∣ A - u * B) (hanchor : N ∣ e - u * f) :
    N ∣ f * A - e * B := by
  have h := dvd_sub (dvd_mul_of_dvd_right hvalue f) (dvd_mul_of_dvd_right hanchor B)
  rw [show f * A - e * B = f * (A - u * B) - B * (e - u * f) by ring]
  exact h

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Compare actual Kummer classes with the same coefficient power, retaining
arithmetic unit corrections and without identifying the anchor exponents. -/
theorem cross_determinant_dvd_of_classes (v : Valuation K ℤᵐ⁰)
    (N m u : ℕ) [HasKummerRoots N K Ω] (x y q r c d : Kˣ)
    (hc : v (c : K) = 1) (hd : v (d : K) = 1)
    (hvalue : kummer N K Ω (x ^ m) =
      kummer N K Ω c * kummer N K Ω (y ^ m) ^ u)
    (hanchor : kummer N K Ω q = kummer N K Ω d * kummer N K Ω r ^ u) :
    (N : ℤ) ∣ (m : ℤ) * (exponent v (r : K) * exponent v (x : K) -
      exponent v (q : K) * exponent v (y : K)) := by
  have hc0 : exponent v (c : K) = 0 := by simp [exponent, hc]
  have hd0 : exponent v (d : K) = 0 := by simp [exponent, hd]
  have hv : (N : ℤ) ∣ (m : ℤ) * exponent v (x : K) -
      (u : ℤ) * ((m : ℤ) * exponent v (y : K)) := by
    have h := exponent_sub_dvd_of_power v (pow_ne_zero m x.ne_zero)
      (c * (y ^ m) ^ u).ne_zero N
      (power_ratio_of_kummer_eq N (x ^ m) (c * (y ^ m) ^ u) (by
        simpa only [map_mul, map_pow] using hvalue))
    simpa only [exponent_mul_units, Units.val_pow_eq_pow_val, exponent_pow,
      hc0, zero_add] using h
  have hq : (N : ℤ) ∣ exponent v (q : K) - (u : ℤ) * exponent v (r : K) := by
    have h := exponent_sub_dvd_of_power v q.ne_zero (d * r ^ u).ne_zero N
      (power_ratio_of_kummer_eq N q (d * r ^ u) (by
        simpa only [map_mul, map_pow] using hanchor))
    simpa only [exponent_mul_units, Units.val_pow_eq_pow_val, exponent_pow,
      hd0, zero_add] using h
  have h := dvd_cross_determinant N ((m : ℤ) * exponent v (x : K))
    ((m : ℤ) * exponent v (y : K)) (exponent v (q : K)) (exponent v (r : K)) u hv hq
  convert h using 1; ring

theorem cross_determinant_eq_zero_of_finite_comparison (v : Valuation K ℤᵐ⁰)
    (N m u : ℕ) (hm : m ≠ 0) [HasKummerRoots N K Ω] (x y q r c d : Kˣ)
    (hc : v (c : K) = 1) (hd : v (d : K) = 1)
    (hbound : ((m : ℤ) * (exponent v (r : K) * exponent v (x : K) -
      exponent v (q : K) * exponent v (y : K))).natAbs < N)
    (hvalue : kummer N K Ω (x ^ m) =
      kummer N K Ω c * kummer N K Ω (y ^ m) ^ u)
    (hanchor : kummer N K Ω q = kummer N K Ω d * kummer N K Ω r ^ u) :
    exponent v (r : K) * exponent v (x : K) =
      exponent v (q : K) * exponent v (y : K) := by
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (cross_determinant_dvd_of_classes v N m u x y q r c d hc hd hvalue hanchor)
    (by simpa using hbound)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
    (by exact_mod_cast hm : (m : ℤ) ≠ 0))

/-- At each level the exponent and the two unit corrections may change.
No coherence of their choices and no a priori finite bound are assumed. -/
theorem cross_determinant_eq_zero_of_tower (v : Valuation K ℤᵐ⁰)
    (m ell : ℕ) (hm : m ≠ 0) (hell : 1 < ell) (x y q r : Kˣ)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) K Ω)
    (hcompare : ∀ k : ℕ, letI := roots k
      ∃ (u : ℕ) (c d : Kˣ), v (c : K) = 1 ∧ v (d : K) = 1 ∧
        kummer (ell ^ k) K Ω (x ^ m) =
          kummer (ell ^ k) K Ω c * kummer (ell ^ k) K Ω (y ^ m) ^ u ∧
        kummer (ell ^ k) K Ω q =
          kummer (ell ^ k) K Ω d * kummer (ell ^ k) K Ω r ^ u) :
    exponent v (r : K) * exponent v (x : K) =
      exponent v (q : K) * exponent v (y : K) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    ((m : ℤ) * (exponent v (r : K) * exponent v (x : K) -
      exponent v (q : K) * exponent v (y : K))).natAbs hell
  let _ := roots k
  obtain ⟨u, c, d, hc, hd, hvalue, hanchor⟩ := hcompare k
  exact cross_determinant_eq_zero_of_finite_comparison v (ell ^ k) m u hm
    x y q r c d hc hd hk hvalue hanchor

/-- Independent calibration restores absolute principal lattices. -/
theorem principal_eq_of_calibrated_cross_determinant (v : Valuation K ℤᵐ⁰)
    (x y q r : Kˣ) (he : exponent v (q : K) ≠ 0)
    (hr : exponent v (q : K) = exponent v (r : K))
    (hdet : exponent v (r : K) * exponent v (x : K) =
      exponent v (q : K) * exponent v (y : K)) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  rw [← hr] at hdet
  exact principal_eq_of_exponent_eq v x.ne_zero y.ne_zero (mul_left_cancel₀ he hdet)

/-- A quadratic label is scale independent once both anchor exponents are
nonzero. This does not assert equality of the anchors or absolute lattices. -/
theorem quadratic_labels_eq_of_cross_determinant (v : Valuation K ℤᵐ⁰)
    (q r : Kˣ) (hq : exponent v (q : K) ≠ 0) (hr : exponent v (r : K) ≠ 0)
    (i j : ℕ)
    (hdet : exponent v (r : K) * exponent v ((q ^ (i ^ 2) : Kˣ) : K) =
      exponent v (q : K) * exponent v ((r ^ (j ^ 2) : Kˣ) : K)) : i = j := by
  simp only [Units.val_pow_eq_pow_val, exponent_pow] at hdet
  have hs : (exponent v (q : K) * exponent v (r : K)) * ((i ^ 2 : ℕ) : ℤ) =
      (exponent v (q : K) * exponent v (r : K)) * ((j ^ 2 : ℕ) : ℤ) := by
    convert hdet using 1 <;> ring
  have hs' : i ^ 2 = j ^ 2 := by
    exact_mod_cast mul_left_cancel₀ (mul_ne_zero hq hr) hs
  nlinarith

/-- An explicit independent determinant bound for finite quadratic labels. -/
theorem quadratic_determinant_bound (v : Valuation K ℤᵐ⁰) (q r : Kˣ)
    (m i j J : ℕ) (hi : i ≤ J) (hj : j ≤ J) :
    ((m : ℤ) * (exponent v (r : K) * exponent v ((q ^ (i ^ 2) : Kˣ) : K) -
      exponent v (q : K) * exponent v ((r ^ (j ^ 2) : Kˣ) : K))).natAbs ≤
        m * (exponent v (q : K)).natAbs * (exponent v (r : K)).natAbs * J ^ 2 := by
  have hi2 := Nat.pow_le_pow_left hi 2
  have hj2 := Nat.pow_le_pow_left hj 2
  have hab : (((i ^ 2 : ℕ) : ℤ) - ((j ^ 2 : ℕ) : ℤ)).natAbs ≤ J ^ 2 := by omega
  simp only [Units.val_pow_eq_pow_val, exponent_pow]
  rw [show (m : ℤ) * (exponent v (r : K) * (((i ^ 2 : ℕ) : ℤ) * exponent v (q : K)) -
      exponent v (q : K) * (((j ^ 2 : ℕ) : ℤ) * exponent v (r : K))) =
      ((m : ℤ) * exponent v (q : K) * exponent v (r : K)) *
        (((i ^ 2 : ℕ) : ℤ) - ((j ^ 2 : ℕ) : ℤ)) by ring]
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ hab

theorem quadratic_labels_eq_of_finite_comparison (v : Valuation K ℤᵐ⁰)
    (N m u : ℕ) (hm : m ≠ 0) [HasKummerRoots N K Ω] (q r c d : Kˣ)
    (hq : exponent v (q : K) ≠ 0) (hr : exponent v (r : K) ≠ 0)
    (hc : v (c : K) = 1) (hd : v (d : K) = 1)
    (i j J : ℕ) (hi : i ≤ J) (hj : j ≤ J)
    (hprecision : m * (exponent v (q : K)).natAbs *
      (exponent v (r : K)).natAbs * J ^ 2 < N)
    (hvalue : kummer N K Ω ((q ^ (i ^ 2)) ^ m) =
      kummer N K Ω c * kummer N K Ω ((r ^ (j ^ 2)) ^ m) ^ u)
    (hanchor : kummer N K Ω q = kummer N K Ω d * kummer N K Ω r ^ u) : i = j := by
  apply quadratic_labels_eq_of_cross_determinant v q r hq hr i j
  exact cross_determinant_eq_zero_of_finite_comparison v N m u hm
    (q ^ (i ^ 2)) (r ^ (j ^ 2)) q r c d hc hd
    (lt_of_le_of_lt (quadratic_determinant_bound v q r m i j J hi hj) hprecision)
    hvalue hanchor

/-- Even both exact comparisons at every 3-power level leave an absolute-scale
ambiguity if the anchors themselves have different valuations. -/
theorem unequal_anchors_lose_absolute_scale (v : Valuation K ℤᵐ⁰) (q : Kˣ)
    (he : exponent v (q : K) ≠ 0) (k : ℕ) [HasKummerRoots (3 ^ k) K Ω] :
    Nat.Coprime 4 (3 ^ k) ∧
      kummer (3 ^ k) K Ω (q ^ 4) = kummer (3 ^ k) K Ω q ^ 4 ∧
      exponent v (q : K) * exponent v ((q ^ 4 : Kˣ) : K) =
        exponent v ((q ^ 4 : Kˣ) : K) * exponent v (q : K) ∧
      ((q ^ 4 : Kˣ) : K) • integerRegion v ≠ (q : K) • integerRegion v := by
  obtain ⟨hcop, hclass, hneq⟩ := unanchored_unit_power_fails (Ω := Ω) v q he k
  exact ⟨hcop, hclass, mul_comm _ _, hneq⟩

end CoreProjectiveComparison

#print axioms CoreProjectiveComparison.dvd_cross_determinant
#print axioms CoreProjectiveComparison.cross_determinant_dvd_of_classes
#print axioms CoreProjectiveComparison.cross_determinant_eq_zero_of_finite_comparison
#print axioms CoreProjectiveComparison.cross_determinant_eq_zero_of_tower
#print axioms CoreProjectiveComparison.principal_eq_of_calibrated_cross_determinant
#print axioms CoreProjectiveComparison.quadratic_labels_eq_of_cross_determinant
#print axioms CoreProjectiveComparison.quadratic_determinant_bound
#print axioms CoreProjectiveComparison.quadratic_labels_eq_of_finite_comparison
#print axioms CoreProjectiveComparison.unequal_anchors_lose_absolute_scale
