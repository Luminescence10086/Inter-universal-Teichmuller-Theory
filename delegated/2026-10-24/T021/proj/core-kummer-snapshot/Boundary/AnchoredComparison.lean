import Boundary.Frontier

/-! A shared cyclotomic power ambiguity can be calibrated by a nonzero-valuation
anchor. All comparisons below concern the actual continuous Kummer map.
The anchor comparison is an independent source obligation, not constructed here.
No assertion about a Hodge theater or an original IUT arrow is made. -/
set_option autoImplicit false

namespace CoreAnchoredComparison
open KummerTheory CoreDiscreteKummer
open scoped WithZero Pointwise

/-- Eliminate the same unknown scalar from a value and its calibrated anchor. -/
theorem dvd_determinant (N A B e u : ℤ)
    (hvalue : N ∣ A - u * B) (hanchor : N ∣ e - u * e) :
    N ∣ e * (A - B) := by
  have h := dvd_sub (dvd_mul_of_dvd_right hvalue e) (dvd_mul_of_dvd_right hanchor B)
  rw [show e * (A - B) = e * (A - u * B) - B * (e - u * e) by ring]
  exact h

theorem cancel_anchor_precision (m n : ℕ) (hm : m ≠ 0) (e d : ℤ) (he : e ≠ 0)
    (h : ((m * n * e.natAbs : ℕ) : ℤ) ∣ (m : ℤ) * e * d) : (n : ℤ) ∣ d := by
  have hnat := Int.natCast_dvd.mp h
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnat
  have hcancel : (m * e.natAbs) * n ∣ (m * e.natAbs) * d.natAbs := by
    convert hnat using 1; ring
  exact Int.natCast_dvd.mpr
    ((mul_dvd_mul_iff_left (Nat.mul_ne_zero hm (Int.natAbs_ne_zero.mpr he))).mp hcancel)

section CoefficientPower
variable {G M : Type*} [Group G] [TopologicalSpace G]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- The actual map on H1 induced by raising the coefficient module to u. -/
noncomputable def coefficientPower (u : ℕ) : ContH1 G M →* ContH1 G M :=
  ContH1.map (MonoidHom.id G) continuous_id (powMonoidHom u) (continuous_pow u)
    (fun g z => (smul_pow' g z u).symm)

theorem coefficientPower_eq_pow (u : ℕ) (c : ContH1 G M) :
    coefficientPower u c = c ^ u := by
  induction c using ContH1.induction_on with
  | h c =>
    erw [coefficientPower, ContH1.map_mk, ← map_pow]
    congr 1
end CoefficientPower

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem exponent_mul_units (v : Valuation K ℤᵐ⁰) (x y : Kˣ) :
    exponent v ((x * y : Kˣ) : K) = exponent v (x : K) + exponent v (y : K) := by
  simp only [exponent, Units.val_mul, map_mul]
  exact WithZero.log_mul (v.ne_zero_iff.mpr x.ne_zero) (v.ne_zero_iff.mpr y.ne_zero)

/-- The valuation-one condition is the arithmetic content needed from O^x;
it does not assert that the unit's finite Kummer class is trivial. -/
theorem cross_difference_dvd_of_unit_corrected_classes (v : Valuation K ℤᵐ⁰)
    (N m u : ℕ) [HasKummerRoots N K Ω] (x y q r c d : Kˣ)
    (hc : v (c : K) = 1) (hd : v (d : K) = 1)
    (hr : exponent v (q : K) = exponent v (r : K))
    (hvalue : kummer N K Ω (x ^ m) =
      kummer N K Ω c * kummer N K Ω (y ^ m) ^ u)
    (hanchor : kummer N K Ω q = kummer N K Ω d * kummer N K Ω r ^ u) :
    (N : ℤ) ∣ (m : ℤ) * exponent v (q : K) *
      (exponent v (x : K) - exponent v (y : K)) := by
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
  have hq : (N : ℤ) ∣ exponent v (q : K) - (u : ℤ) * exponent v (q : K) := by
    have h := exponent_sub_dvd_of_power v q.ne_zero (d * r ^ u).ne_zero N
      (power_ratio_of_kummer_eq N q (d * r ^ u) (by
        simpa only [map_mul, map_pow] using hanchor))
    simpa only [exponent_mul_units, Units.val_pow_eq_pow_val, exponent_pow,
      hd0, zero_add, ← hr] using h
  have h := dvd_determinant (N : ℤ) ((m : ℤ) * exponent v (x : K))
    ((m : ℤ) * exponent v (y : K)) (exponent v (q : K)) u hv hq
  convert h using 1; ring

theorem principal_eq_of_unit_corrected_anchored_classes (v : Valuation K ℤᵐ⁰)
    (m n u : ℕ) (hm : m ≠ 0) (x y q r c d : Kˣ)
    (he : exponent v (q : K) ≠ 0)
    (hc : v (c : K) = 1) (hd : v (d : K) = 1)
    (hr : exponent v (q : K) = exponent v (r : K))
    [HasKummerRoots (m * n * (exponent v (q : K)).natAbs) K Ω]
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (hvalue : kummer (m * n * (exponent v (q : K)).natAbs) K Ω (x ^ m) =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω c *
        kummer (m * n * (exponent v (q : K)).natAbs) K Ω (y ^ m) ^ u)
    (hanchor : kummer (m * n * (exponent v (q : K)).natAbs) K Ω q =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω d *
        kummer (m * n * (exponent v (q : K)).natAbs) K Ω r ^ u) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  apply principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
  apply sub_eq_zero.mp
  have hdiv : (n : ℤ) ∣ exponent v (x : K) - exponent v (y : K) :=
    cancel_anchor_precision m n hm (exponent v (q : K)) _ he
      (cross_difference_dvd_of_unit_corrected_classes v _ m u x y q r c d hc hd hr
        hvalue hanchor)
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by simpa using hbound)

/-- The two actual class comparisons imply an integral determinant congruence. -/
theorem cross_difference_dvd_of_classes (v : Valuation K ℤᵐ⁰)
    (N m u : ℕ) [HasKummerRoots N K Ω] (x y q r : Kˣ)
    (hr : exponent v (q : K) = exponent v (r : K))
    (hvalue : kummer N K Ω (x ^ m) = kummer N K Ω (y ^ m) ^ u)
    (hanchor : kummer N K Ω q = kummer N K Ω r ^ u) :
    (N : ℤ) ∣ (m : ℤ) * exponent v (q : K) *
      (exponent v (x : K) - exponent v (y : K)) := by
  have hv : (N : ℤ) ∣ (m : ℤ) * exponent v (x : K) -
      (u : ℤ) * ((m : ℤ) * exponent v (y : K)) := by
    have h := exponent_sub_dvd_of_power v (pow_ne_zero m x.ne_zero)
      (pow_ne_zero u (pow_ne_zero m y.ne_zero)) N
      (power_ratio_of_kummer_eq N (x ^ m) ((y ^ m) ^ u) (by
        simpa only [map_pow] using hvalue))
    simpa only [Units.val_pow_eq_pow_val, exponent_pow] using h
  have hq : (N : ℤ) ∣ exponent v (q : K) - (u : ℤ) * exponent v (q : K) := by
    have h := exponent_sub_dvd_of_power v q.ne_zero (pow_ne_zero u r.ne_zero) N
      (power_ratio_of_kummer_eq N q (r ^ u) (by
        simpa only [map_pow] using hanchor))
    simpa only [Units.val_pow_eq_pow_val, exponent_pow, ← hr] using h
  have h := dvd_determinant (N : ℤ) ((m : ℤ) * exponent v (x : K))
    ((m : ℤ) * exponent v (y : K)) (exponent v (q : K)) u hv hq
  convert h using 1; ring

/-- Finite precision with an explicitly synchronized anchor. The exponent u may
be arbitrary: invertibility of the coefficient power is not used. The cost
m*n*|v(q)| is sufficient, not claimed minimal. q and r need only have equal
nonzero valuation; they are not assumed equal as elements or Kummer classes. -/
theorem exponent_sub_dvd_of_anchored_classes (v : Valuation K ℤᵐ⁰)
    (m n u : ℕ) (hm : m ≠ 0) (x y q r : Kˣ)
    (he : exponent v (q : K) ≠ 0)
    (hr : exponent v (q : K) = exponent v (r : K))
    [HasKummerRoots (m * n * (exponent v (q : K)).natAbs) K Ω]
    (hvalue : kummer (m * n * (exponent v (q : K)).natAbs) K Ω (x ^ m) =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω (y ^ m) ^ u)
    (hanchor : kummer (m * n * (exponent v (q : K)).natAbs) K Ω q =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω r ^ u) :
    (n : ℤ) ∣ exponent v (x : K) - exponent v (y : K) := by
  apply cancel_anchor_precision m n hm (exponent v (q : K))
    (exponent v (x : K) - exponent v (y : K)) he
  exact cross_difference_dvd_of_classes v _ m u x y q r hr hvalue hanchor

theorem principal_eq_of_anchored_classes_and_bound (v : Valuation K ℤᵐ⁰)
    (m n u : ℕ) (hm : m ≠ 0) (x y q r : Kˣ)
    (he : exponent v (q : K) ≠ 0)
    (hr : exponent v (q : K) = exponent v (r : K))
    [HasKummerRoots (m * n * (exponent v (q : K)).natAbs) K Ω]
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (hvalue : kummer (m * n * (exponent v (q : K)).natAbs) K Ω (x ^ m) =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω (y ^ m) ^ u)
    (hanchor : kummer (m * n * (exponent v (q : K)).natAbs) K Ω q =
      kummer (m * n * (exponent v (q : K)).natAbs) K Ω r ^ u) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  apply principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (exponent_sub_dvd_of_anchored_classes v m n u hm x y q r he hr hvalue hanchor)
    (by simpa using hbound)

/-- An unbounded tower needs neither a finite bound nor fixed exponents u_k.
Only the same u_k must act on the value and anchor at each individual level. -/
theorem principal_eq_of_anchored_tower (v : Valuation K ℤᵐ⁰)
    (m ell : ℕ) (hm : m ≠ 0) (hell : 1 < ell) (x y q r : Kˣ)
    (he : exponent v (q : K) ≠ 0)
    (hr : exponent v (q : K) = exponent v (r : K))
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) K Ω)
    (hcompare : ∀ k : ℕ, letI := roots k
      ∃ u : ℕ, kummer (ell ^ k) K Ω (x ^ m) =
          kummer (ell ^ k) K Ω (y ^ m) ^ u ∧
        kummer (ell ^ k) K Ω q = kummer (ell ^ k) K Ω r ^ u) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  let d := (m : ℤ) * exponent v (q : K) *
    (exponent v (x : K) - exponent v (y : K))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt d.natAbs hell
  let _ := roots k
  obtain ⟨u, hvalue, hanchor⟩ := hcompare k
  have hd : d = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (cross_difference_dvd_of_classes v (ell ^ k) m u x y q r hr hvalue hanchor)
    (by simpa using hk)
  have hzero := (mul_eq_zero.mp hd).resolve_left
    (mul_ne_zero (by exact_mod_cast hm : (m : ℤ) ≠ 0) he)
  exact principal_eq_of_exponent_eq v x.ne_zero y.ne_zero (sub_eq_zero.mp hzero)

/-- Equality of the actual principal sets also reflects their exponents. -/
theorem exponent_eq_of_principal_eq (v : Valuation K ℤᵐ⁰) (x y : Kˣ)
    (h : (x : K) • integerRegion v = (y : K) • integerRegion v) :
    exponent v (x : K) = exponent v (y : K) := by
  have hx : (x : K) ∈ (x : K) • integerRegion v :=
    (mem_principal_iff v x.ne_zero _).mpr le_rfl
  have hy : (y : K) ∈ (y : K) • integerRegion v :=
    (mem_principal_iff v y.ne_zero _).mpr le_rfl
  rw [h] at hx
  rw [← h] at hy
  exact congrArg WithZero.log (le_antisymm
    ((mem_principal_iff v y.ne_zero _).mp hx)
    ((mem_principal_iff v x.ne_zero _).mp hy))

/-- A negative control: even a 3-power tower with coprime coefficient exponent
4 cannot distinguish q and q^4 up to that coefficient action. Their actual
principal sets differ whenever the anchor has nonzero valuation. -/
theorem unanchored_unit_power_fails (v : Valuation K ℤᵐ⁰) (q : Kˣ)
    (he : exponent v (q : K) ≠ 0) (k : ℕ) [HasKummerRoots (3 ^ k) K Ω] :
    Nat.Coprime 4 (3 ^ k) ∧
      kummer (3 ^ k) K Ω (q ^ 4) = kummer (3 ^ k) K Ω q ^ 4 ∧
      ((q ^ 4 : Kˣ) : K) • integerRegion v ≠ (q : K) • integerRegion v := by
  refine ⟨(by norm_num : Nat.Coprime 4 3).pow_right k, map_pow _ _ _, ?_⟩
  intro h
  have hh := exponent_eq_of_principal_eq v (q ^ 4) q h
  simp only [Units.val_pow_eq_pow_val, exponent_pow] at hh
  apply he
  omega

/-- An explicit source-independent bound for a fixed finite theta-label range.
This is the q^(j^2) shape of lgpValue; no wall or Hodge transport is assumed. -/
theorem quadratic_label_bound (v : Valuation K ℤᵐ⁰) (q : Kˣ)
    (i j J : ℕ) (hi : i ≤ J) (hj : j ≤ J) :
    (exponent v ((q ^ (i ^ 2) : Kˣ) : K) -
      exponent v ((q ^ (j ^ 2) : Kˣ) : K)).natAbs ≤
        (exponent v (q : K)).natAbs * J ^ 2 := by
  have hi2 : i ^ 2 ≤ J ^ 2 := Nat.pow_le_pow_left hi 2
  have hj2 : j ^ 2 ≤ J ^ 2 := Nat.pow_le_pow_left hj 2
  have hab : (((i ^ 2 : ℕ) : ℤ) - ((j ^ 2 : ℕ) : ℤ)).natAbs ≤ J ^ 2 := by
    omega
  simp only [Units.val_pow_eq_pow_val, exponent_pow]
  rw [show ((i ^ 2 : ℕ) : ℤ) * exponent v (q : K) -
      ((j ^ 2 : ℕ) : ℤ) * exponent v (q : K) =
      exponent v (q : K) * (((i ^ 2 : ℕ) : ℤ) - ((j ^ 2 : ℕ) : ℤ)) by ring,
    Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ hab

end CoreAnchoredComparison

namespace CoreAnchoredDecomposition
open IsLocalRing KummerTheory KummerTheory.Decomposition

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ =
    algebraMap k (ResidueField A) c)
  [IsGalois F Ω] [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  (hres : ∀ (a : F) (ha : algebraMap F Ω a ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)

include hres in
/-- Reflect an actual powered reduced comparison through the surjective
decomposition map. The coefficient reduction need not be invertible. Apply
this separately to the value and its anchor, retaining the same u. -/
theorem residue_kummer_pow_of_reduced_comparison
    (n u : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]
    [HasKummerRoots n k (ResidueField A)]
    (f g : Fˣ) (a b : kˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hg : algebraMap F Ω g ∈ A) (hg' : algebraMap F Ω ↑g⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) a)
    (hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) b)
    (hcompare : CoreDecompositionBridge.reducedClass A hk hkres n hn f =
      CoreDecompositionBridge.reducedClass A hk hkres n hn g ^ u) :
    kummer n k (ResidueField A) a = kummer n k (ResidueField A) b ^ u := by
  let _ := muAction F A hk hkres n
  apply CoreReducedComparison.pullback_injective (decompositionMap F A hk hkres)
    (continuous_decompositionMap F A hk hkres)
    (decompositionMap_surjective (F := F) A hk hkres hres) (fun _ _ => rfl)
  rw [map_pow]
  exact (decomposition_kummer F A hk hkres n hn f a hf hf' hfa).symm.trans
    (hcompare.trans (congrArg (fun c => c ^ u)
      (decomposition_kummer F A hk hkres n hn g b hg hg' hgb)))

end CoreAnchoredDecomposition

#print axioms CoreAnchoredComparison.dvd_determinant
#print axioms CoreAnchoredComparison.cancel_anchor_precision
#print axioms CoreAnchoredComparison.coefficientPower
#print axioms CoreAnchoredComparison.coefficientPower_eq_pow
#print axioms CoreAnchoredComparison.exponent_mul_units
#print axioms CoreAnchoredComparison.cross_difference_dvd_of_unit_corrected_classes
#print axioms CoreAnchoredComparison.principal_eq_of_unit_corrected_anchored_classes
#print axioms CoreAnchoredComparison.cross_difference_dvd_of_classes
#print axioms CoreAnchoredComparison.exponent_sub_dvd_of_anchored_classes
#print axioms CoreAnchoredComparison.principal_eq_of_anchored_classes_and_bound
#print axioms CoreAnchoredComparison.principal_eq_of_anchored_tower
#print axioms CoreAnchoredComparison.exponent_eq_of_principal_eq
#print axioms CoreAnchoredComparison.unanchored_unit_power_fails
#print axioms CoreAnchoredComparison.quadratic_label_bound
#print axioms CoreAnchoredDecomposition.residue_kummer_pow_of_reduced_comparison
