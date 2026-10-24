import ContinuousKummerTheory.Kummer.Equiv
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import CohomologyReflection
import ContinuousKummerTheory.Kummer.DecompositionSurjective
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.KrullDimension.PID

/- Source section: Boundary/DiscreteValuation.lean -/
/-! Kummer separation over any integer-valued field, including genuine finite-place
completions. No assumption that the field equals Qp or has ramification index one.
The log below is the integer exponent of a multiplicative valuation, not real log. -/
set_option autoImplicit false

namespace CoreDiscreteKummer
open scoped WithZero Pointwise
open KummerTheory

variable {K : Type*} [Field K]

def exponent (v : Valuation K ℤᵐ⁰) (x : K) : ℤ := WithZero.log (v x)

theorem exponent_pow (v : Valuation K ℤᵐ⁰) (x : K) (n : ℕ) :
    exponent v (x ^ n) = (n : ℤ) * exponent v x := by
  simp [exponent, map_pow, WithZero.log_pow]

theorem exponent_sub_dvd_of_power (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (h : ∃ z : K, x / y = z ^ n) :
    (n : ℤ) ∣ exponent v x - exponent v y := by
  obtain ⟨z, hz⟩ := h
  have hv : exponent v (x / y) = exponent v x - exponent v y := by
    simp only [exponent, map_div₀, WithZero.log_div (v.ne_zero_iff.mpr hx)
      (v.ne_zero_iff.mpr hy)]
  refine ⟨exponent v z, ?_⟩
  rw [← hv, hz, exponent_pow]

theorem exponent_eq_of_bounded_power (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ)
    (hbound : (exponent v x - exponent v y).natAbs < n)
    (h : ∃ z : K, x / y = z ^ n) : exponent v x = exponent v y := by
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (exponent_sub_dvd_of_power v hx hy n h) (by simpa using hbound)

theorem exponent_eq_of_power_tower (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (h : ∀ k : ℕ, ∃ z : K, x / y = z ^ (ell ^ k)) :
    exponent v x = exponent v y := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (exponent v x - exponent v y).natAbs hell
  exact exponent_eq_of_bounded_power v hx hy (ell ^ k) hk (h k)

theorem valuation_eq_of_exponent_eq (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : exponent v x = exponent v y) : v x = v y := by
  have := congrArg (WithZero.exp : ℤ → ℤᵐ⁰) h
  simpa only [exponent, WithZero.exp_log (v.ne_zero_iff.mpr hx),
    WithZero.exp_log (v.ne_zero_iff.mpr hy)] using this

/-- The actual valuation subring, not an independently postulated lattice. -/
def integerRegion (v : Valuation K ℤᵐ⁰) : Set K := v.valuationSubring

theorem mem_principal_iff (v : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) (z : K) :
    z ∈ x • integerRegion v ↔ v z ≤ v x := by
  have hmem : z ∈ x • integerRegion v ↔ z / x ∈ integerRegion v := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa only [smul_eq_mul, mul_div_cancel_left₀ a hx] using ha
    · intro h
      exact ⟨z / x, h, by
        change x * (z / x) = z
        exact mul_div_cancel₀ z hx⟩
  rw [hmem]
  change v (z / x) ≤ 1 ↔ v z ≤ v x
  rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hx))]

theorem principal_eq_of_exponent_eq (v : Valuation K ℤᵐ⁰)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : exponent v x = exponent v y) :
    x • integerRegion v = y • integerRegion v := by
  ext z
  rw [mem_principal_iff v hx, mem_principal_iff v hy,
    valuation_eq_of_exponent_eq v hx hy h]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem power_ratio_of_kummer_eq (n : ℕ) [HasKummerRoots n K Ω]
    (x y : Kˣ) (h : kummer n K Ω x = kummer n K Ω y) :
    ∃ z : K, (x : K) / (y : K) = z ^ n := by
  have hker : x / y ∈ (kummer n K Ω).ker := by
    rw [MonoidHom.mem_ker, map_div, h, div_self']
  rw [ker_kummer] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨(z : K), ?_⟩
  simpa only [powMonoidHom_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    using (congrArg (fun u : Kˣ => (u : K)) hz).symm

theorem principal_eq_of_kummer_eq_and_bound (v : Valuation K ℤᵐ⁰)
    (n : ℕ) [HasKummerRoots n K Ω] (x y : Kˣ)
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (h : kummer n K Ω x = kummer n K Ω y) :
    (x : K) • integerRegion v = (y : K) • integerRegion v :=
  principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
    (exponent_eq_of_bounded_power v x.ne_zero y.ne_zero n hbound
      (power_ratio_of_kummer_eq n x y h))

theorem principal_eq_of_normalized_kummer_tower (v : Valuation K ℤᵐ⁰)
    (m : ℕ) (hm : m ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) K Ω) (x y : Kˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) K Ω (x ^ m) = kummer (ell ^ k) K Ω (y ^ m)) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  have hv : exponent v ((x : K) ^ m) = exponent v ((y : K) ^ m) := by
    apply exponent_eq_of_power_tower v (pow_ne_zero m x.ne_zero)
      (pow_ne_zero m y.ne_zero) ell hell
    intro k
    let _ := roots k
    simpa only [Units.val_pow_eq_pow_val] using
      power_ratio_of_kummer_eq (ell ^ k) (x ^ m) (y ^ m) (h k)
  rw [exponent_pow, exponent_pow] at hv
  exact principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
    (mul_left_cancel₀ (by exact_mod_cast hm : (m : ℤ) ≠ 0) hv)

end CoreDiscreteKummer

#print axioms CoreDiscreteKummer.exponent
#print axioms CoreDiscreteKummer.exponent_pow
#print axioms CoreDiscreteKummer.exponent_sub_dvd_of_power
#print axioms CoreDiscreteKummer.exponent_eq_of_bounded_power
#print axioms CoreDiscreteKummer.exponent_eq_of_power_tower
#print axioms CoreDiscreteKummer.valuation_eq_of_exponent_eq
#print axioms CoreDiscreteKummer.integerRegion
#print axioms CoreDiscreteKummer.mem_principal_iff
#print axioms CoreDiscreteKummer.principal_eq_of_exponent_eq
#print axioms CoreDiscreteKummer.power_ratio_of_kummer_eq
#print axioms CoreDiscreteKummer.principal_eq_of_kummer_eq_and_bound
#print axioms CoreDiscreteKummer.principal_eq_of_normalized_kummer_tower

/- Source section: Boundary/FinitePlace.lean -/
/-! Concrete instantiation on the canonical completions at finite number-field
places. The field is definitionally the same expression as IUT's completionAt,
but this file does not import or instantiate a Hodge theater. -/
set_option autoImplicit false

namespace CoreFinitePlaceKummer
open scoped WithZero Pointwise
open NumberField IsDedekindDomain KummerTheory CoreDiscreteKummer

variable {K : Type*} [Field K] [NumberField K]

noncomputable abbrev fieldAt (w : FinitePlace K) := w.maximalIdeal.adicCompletion K

noncomputable def localValuation (w : FinitePlace K) : Valuation (fieldAt w) ℤᵐ⁰ := Valued.v

theorem integerRegion_eq (w : FinitePlace K) :
    integerRegion (localValuation w) =
      (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) := rfl

theorem integerRing_isDVR (w : FinitePlace K) :
    IsDiscreteValuationRing (w.maximalIdeal.adicCompletionIntegers K) := inferInstance

theorem mem_principal_iff (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0)
    (z : fieldAt w) :
    z ∈ x • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) ↔
      localValuation w z ≤ localValuation w x :=
  CoreDiscreteKummer.mem_principal_iff (localValuation w) hx z

variable {Ω : Type*} [Field Ω]

theorem principal_eq_of_normalized_kummer_tower (w : FinitePlace K)
    [Algebra (fieldAt w) Ω] [IsGalois (fieldAt w) Ω]
    (m : ℕ) (hm : m ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) (fieldAt w) Ω)
    (x y : (fieldAt w)ˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) (fieldAt w) Ω (x ^ m) =
        kummer (ell ^ k) (fieldAt w) Ω (y ^ m)) :
    (x : fieldAt w) • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) =
      (y : fieldAt w) • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) :=
  CoreDiscreteKummer.principal_eq_of_normalized_kummer_tower
    (localValuation w) m hm ell hell roots x y h

end CoreFinitePlaceKummer

#print axioms CoreFinitePlaceKummer.fieldAt
#print axioms CoreFinitePlaceKummer.localValuation
#print axioms CoreFinitePlaceKummer.integerRegion_eq
#print axioms CoreFinitePlaceKummer.integerRing_isDVR
#print axioms CoreFinitePlaceKummer.mem_principal_iff
#print axioms CoreFinitePlaceKummer.principal_eq_of_normalized_kummer_tower

/- Source section: Boundary/ReducedComparison.lean -/
/-! Reflection of the residue-side class does not require invertibility of the
coefficient-reduction map on the other side of a specialization square. -/
set_option autoImplicit false

namespace CoreReducedComparison

section Reflection
variable {G H M : Type*}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]

theorem pullback_injective (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ)
    (hcomp : ∀ h m, φ h • m = h • m) :
    Function.Injective (ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp) :=
  CoreCohomologyReflection.map_injective φ hφ hsurj (MulEquiv.refl M) continuous_id hcomp

/-- R may be noninjective. Equality after R reflects the right-side classes
through the separately injective pullback, not through an inverse to R. -/
theorem residue_classes_eq_of_specialization_squares
    (φ : H →* G) (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (hcomp : ∀ h m, φ h • m = h • m)
    {C : Type*} (R : C → ContH1 H M) (c d : C) (a b : ContH1 G M)
    (hc : R c = ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp a)
    (hd : R d = ContH1.map φ hφ (MonoidHom.id M) continuous_id hcomp b)
    (hcompare : R c = R d) : a = b := by
  apply pullback_injective φ hφ hsurj hcomp
  exact hc.symm.trans (hcompare.trans hd)

end Reflection

end CoreReducedComparison

#print axioms CoreReducedComparison.pullback_injective
#print axioms CoreReducedComparison.residue_classes_eq_of_specialization_squares

/- Source section: Boundary/PrecisionLoss.lean -/
/-! Exact finite precision cost of a normalization power. Raising the comparison
level from n to m*n recovers n-divisibility of the original valuation difference.
No coprimality or entire infinite tower is needed for this finite certificate. -/
set_option autoImplicit false

namespace CoreKummerPrecision
open scoped WithZero Pointwise
open KummerTheory CoreDiscreteKummer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem exponent_sub_dvd_of_raised_level (v : Valuation K ℤᵐ⁰)
    (m n : ℕ) (hm : m ≠ 0) [HasKummerRoots (m * n) K Ω] (x y : Kˣ)
    (h : kummer (m * n) K Ω (x ^ m) = kummer (m * n) K Ω (y ^ m)) :
    (n : ℤ) ∣ exponent v (x : K) - exponent v (y : K) := by
  have hd := exponent_sub_dvd_of_power v (pow_ne_zero m x.ne_zero)
    (pow_ne_zero m y.ne_zero) (m * n)
    (power_ratio_of_kummer_eq (m * n) (x ^ m) (y ^ m) h)
  rw [exponent_pow, exponent_pow, Nat.cast_mul, ← mul_sub] at hd
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hm : (m : ℤ) ≠ 0)).mp hd

theorem principal_eq_of_raised_level_and_bound (v : Valuation K ℤᵐ⁰)
    (m n : ℕ) (hm : m ≠ 0) [HasKummerRoots (m * n) K Ω] (x y : Kˣ)
    (hbound : (exponent v (x : K) - exponent v (y : K)).natAbs < n)
    (h : kummer (m * n) K Ω (x ^ m) = kummer (m * n) K Ω (y ^ m)) :
    (x : K) • integerRegion v = (y : K) • integerRegion v := by
  apply principal_eq_of_exponent_eq v x.ne_zero y.ne_zero
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (exponent_sub_dvd_of_raised_level v m n hm x y h) (by simpa using hbound)

end CoreKummerPrecision

#print axioms CoreKummerPrecision.exponent_sub_dvd_of_raised_level
#print axioms CoreKummerPrecision.principal_eq_of_raised_level_and_bound

/- Source section: Boundary/DecompositionBridge.lean -/
/-! A rational-point decomposition comparison, instantiated on the actual
restriction, coefficient reduction and residue Kummer maps. Source comparison
is still an explicit obligation; reduceMu is never assumed invertible. -/
set_option autoImplicit false

namespace CoreDecompositionBridge
open IsLocalRing KummerTheory KummerTheory.Decomposition
open scoped WithZero Pointwise

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ =
    algebraMap k (ResidueField A) c)
  [IsGalois F Ω] [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  (hres : ∀ (a : F) (ha : algebraMap F Ω a ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)

noncomputable def reducedClass (n : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]
    (f : Fˣ) : letI := muAction F A hk hkres n
      ContH1 (A.decompositionSubgroup F) (Mu n (ResidueField A)) :=
  let _ := muAction F A hk hkres n
  ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
    (reduceMu A n hn) continuous_of_discreteTopology
    (reduceMu_smul F A hk hkres n hn) (kummer n F Ω f)

include hres in
/-- Equality of reduced restrictions recovers residue-side Kummer classes at a
rational point. It does not recover the unreduced source classes. -/
theorem residue_kummer_eq_of_reduced_restrictions_eq
    (n : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]
    [HasKummerRoots n k (ResidueField A)]
    (f g : Fˣ) (a b : kˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hg : algebraMap F Ω g ∈ A) (hg' : algebraMap F Ω ↑g⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) a)
    (hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) b)
    (hcompare : reducedClass A hk hkres n hn f = reducedClass A hk hkres n hn g) :
    kummer n k (ResidueField A) a = kummer n k (ResidueField A) b := by
  let _ := muAction F A hk hkres n
  apply CoreReducedComparison.pullback_injective (decompositionMap F A hk hkres)
    (continuous_decompositionMap F A hk hkres)
    (decompositionMap_surjective (F := F) A hk hkres hres) (fun _ _ => rfl)
  exact (decomposition_kummer F A hk hkres n hn f a hf hf' hfa).symm.trans
    (hcompare.trans (decomposition_kummer F A hk hkres n hn g b hg hg' hgb))

variable [IsGalois k (ResidueField A)]

include hres in
/-- A finite comparison one normalization-factor higher determines the actual
principal valuation-ring lattice, with an independent bound on the exponents. -/
theorem principal_eq_of_reduced_comparison_and_bound
    (v : Valuation k ℤᵐ⁰) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    [HasKummerRoots (m * n) F Ω] [HasKummerRoots (m * n) k (ResidueField A)]
    (f g : Fˣ) (a b : kˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hg : algebraMap F Ω g ∈ A) (hg' : algebraMap F Ω ↑g⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) (a ^ m))
    (hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) (b ^ m))
    (hbound : (CoreDiscreteKummer.exponent v (a : k) -
      CoreDiscreteKummer.exponent v (b : k)).natAbs < n)
    (hcompare : reducedClass A hk hkres (m * n) (Nat.mul_ne_zero hm hn) f =
      reducedClass A hk hkres (m * n) (Nat.mul_ne_zero hm hn) g) :
    (a : k) • CoreDiscreteKummer.integerRegion v =
      (b : k) • CoreDiscreteKummer.integerRegion v := by
  apply CoreKummerPrecision.principal_eq_of_raised_level_and_bound
    (Ω := ResidueField A) v m n hm a b hbound
  exact residue_kummer_eq_of_reduced_restrictions_eq A hk hkres hres
    (m * n) (Nat.mul_ne_zero hm hn) f g (a ^ m) (b ^ m) hf hf' hg hg' hfa hgb hcompare

end CoreDecompositionBridge

#print axioms KummerTheory.Decomposition.decompositionMap_surjective
#print axioms CoreDecompositionBridge.reducedClass
#print axioms CoreDecompositionBridge.residue_kummer_eq_of_reduced_restrictions_eq
#print axioms CoreDecompositionBridge.principal_eq_of_reduced_comparison_and_bound

/- Source section: Boundary/LaurentPoint.lean -/
/-! Rational residues for an actual Laurent-series germ. The valuation over the
function field is distinct from the arithmetic valuation on the constant field.
The power-series residue calculation follows the elementary argument in
LANA's TateCurvesTheta/Kummer/ThetaGerm.lean (Apache 2.0); no theta analytic
statement or tempered fundamental group is assumed here. -/
set_option autoImplicit false

namespace CoreLaurentPoint
open PowerSeries IsLocalRing

variable {k Ω : Type*} [Field k] [Field Ω]

/-- Fix the coefficient embedding explicitly: Hahn series also admits an algebra
structure induced through power series, equal on coefficients but not definally
the same instance. This makes the scalar-tower parameter unambiguous. -/
noncomputable local instance constantsAlgebra : Algebra k (LaurentSeries k) :=
  (HahnSeries.C : k →+* LaurentSeries k).toAlgebra

noncomputable local instance constantsSMul : SMul k (LaurentSeries k) :=
  constantsAlgebra.toSMul

variable [Algebra (LaurentSeries k) Ω]

noncomputable local instance coefficientAlgebra : Algebra k Ω :=
  ((algebraMap (LaurentSeries k) Ω).comp (algebraMap k (LaurentSeries k))).toAlgebra

local instance coefficientTower : IsScalarTower k (LaurentSeries k) Ω :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := LaurentSeries k) (A := Ω) (fun _ => rfl)

variable (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ =
    algebraMap k (ResidueField A) c)
  (hA : ∀ r : k⟦X⟧,
    algebraMap (LaurentSeries k) Ω (algebraMap k⟦X⟧ (LaurentSeries k) r) ∈ A)
  (hX : residue A ⟨_, hA X⟩ = 0)

theorem constants_compatible (c : k) :
    algebraMap k⟦X⟧ (LaurentSeries k) (C c) = algebraMap k (LaurentSeries k) c := by
  change HahnSeries.ofPowerSeries ℤ k (C c) = HahnSeries.C c
  exact HahnSeries.ofPowerSeries_C (Γ := ℤ) c

include hkres hX in
theorem residue_powerSeries (r : k⟦X⟧) :
    residue A ⟨_, hA r⟩ = algebraMap k (ResidueField A) (constantCoeff r) := by
  have hC : ∀ c : k,
      algebraMap (LaurentSeries k) Ω (algebraMap k⟦X⟧ (LaurentSeries k) (C c)) =
        algebraMap k Ω c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k (LaurentSeries k) Ω, constants_compatible]
  set r' := PowerSeries.mk fun p => coeff (p + 1) r
  have e : (⟨_, hA r⟩ : A) = ⟨_, hA X⟩ * ⟨_, hA r'⟩ + ⟨_, hk (constantCoeff r)⟩ := by
    apply Subtype.ext
    conv_lhs => rw [eq_X_mul_shift_add_const r]
    simp only [map_add, map_mul, hC]
    rfl
  rw [e, map_add, map_mul, hX, zero_mul, zero_add, hkres]

include hX in
omit [Algebra k (ResidueField A)] in
/-- The restriction of a dominating valuation to k((X)) is exactly the canonical
power-series valuation ring. A strict overring of this DVR would be the field,
which would make X invertible despite its zero residue. -/
theorem comap_eq_powerSeries_valuationSubring :
    A.comap (algebraMap (LaurentSeries k) Ω) =
      (ValuationRing.valuation k⟦X⟧ (LaurentSeries k)).valuationSubring := by
  let V := (ValuationRing.valuation k⟦X⟧ (LaurentSeries k)).valuationSubring
  let e := ValuationRing.equivInteger k⟦X⟧ (LaurentSeries k)
  have : IsPrincipalIdealRing V :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have hle : V ≤ A.comap (algebraMap (LaurentSeries k) Ω) := by
    intro a ha
    change a ∈ (ValuationRing.valuation k⟦X⟧ (LaurentSeries k)).integer at ha
    obtain ⟨r, rfl⟩ := (ValuationRing.mem_integer_iff k⟦X⟧ (LaurentSeries k) a).mp ha
    exact hA r
  have hne : A.comap (algebraMap (LaurentSeries k) Ω) ≠ ⊤ := by
    intro htop
    let ξ := algebraMap k⟦X⟧ (LaurentSeries k) X
    have hξ : ξ ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective k⟦X⟧ (LaurentSeries k)).ne
          (PowerSeries.X_ne_zero (R := k))
    have hi : algebraMap (LaurentSeries k) Ω ξ⁻¹ ∈ A := by
      have : ξ⁻¹ ∈ A.comap (algebraMap (LaurentSeries k) Ω) := by
        rw [htop]
        trivial
      exact this
    have he : (⟨_, hA X⟩ : A) * ⟨_, hi⟩ = 1 := by
      apply Subtype.ext
      change algebraMap (LaurentSeries k) Ω ξ * algebraMap (LaurentSeries k) Ω ξ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hξ, map_one]
    have hr := congrArg (residue A) he
    rw [map_mul, hX, zero_mul, map_one] at hr
    exact zero_ne_one hr
  exact (ValuationSubring.eq_of_le_of_ne_top V hle hne).symm

include hkres hX in
theorem rational_residues (a : LaurentSeries k) (ha : algebraMap (LaurentSeries k) Ω a ∈ A) :
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c := by
  have hamem : a ∈ A.comap (algebraMap (LaurentSeries k) Ω) := ha
  rw [comap_eq_powerSeries_valuationSubring A hA hX] at hamem
  obtain ⟨r, hr⟩ := (ValuationRing.mem_integer_iff k⟦X⟧ (LaurentSeries k) a).mp hamem
  subst a
  exact ⟨constantCoeff r, residue_powerSeries A hk hkres hA hX r⟩

variable [IsGalois (LaurentSeries k) Ω] [IsAlgClosed Ω]
  [Algebra.IsIntegral k (ResidueField A)]

include hkres hX in
theorem decompositionMap_surjective_at_germ :
    Function.Surjective
      (KummerTheory.Decomposition.decompositionMap (LaurentSeries k) A hk hkres) :=
  KummerTheory.Decomposition.decompositionMap_surjective A hk hkres
    (rational_residues A hk hkres hA hX)

open scoped WithZero Pointwise
open KummerTheory CoreDiscreteKummer

include hkres hX in
/-- A concrete germ consumer: source functions are actual power-series units,
their residues are computed rather than postulated, and the rational-point
condition is discharged. Arithmetic class comparison and a valuation bound
remain explicit inputs. -/
theorem principal_eq_of_powerSeries_comparison [IsGalois k (ResidueField A)]
    (v : Valuation k ℤᵐ⁰) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    [HasKummerRoots (m * n) (LaurentSeries k) Ω]
    [HasKummerRoots (m * n) k (ResidueField A)]
    (r s : (k⟦X⟧)ˣ) (a b : kˣ)
    (hr : constantCoeff (r : k⟦X⟧) = ((a ^ m : kˣ) : k))
    (hs : constantCoeff (s : k⟦X⟧) = ((b ^ m : kˣ) : k))
    (hbound : (exponent v (a : k) - exponent v (b : k)).natAbs < n)
    (hcompare : CoreDecompositionBridge.reducedClass A hk hkres (m * n)
        (Nat.mul_ne_zero hm hn)
        (Units.map (algebraMap k⟦X⟧ (LaurentSeries k) : k⟦X⟧ →* LaurentSeries k) r) =
      CoreDecompositionBridge.reducedClass A hk hkres (m * n)
        (Nat.mul_ne_zero hm hn)
        (Units.map (algebraMap k⟦X⟧ (LaurentSeries k) : k⟦X⟧ →* LaurentSeries k) s)) :
    (a : k) • integerRegion v = (b : k) • integerRegion v := by
  let f := Units.map (algebraMap k⟦X⟧ (LaurentSeries k) : k⟦X⟧ →* LaurentSeries k) r
  let g := Units.map (algebraMap k⟦X⟧ (LaurentSeries k) : k⟦X⟧ →* LaurentSeries k) s
  have hf : algebraMap (LaurentSeries k) Ω (f : LaurentSeries k) ∈ A := hA r
  have hf' : algebraMap (LaurentSeries k) Ω ((f⁻¹ : (LaurentSeries k)ˣ) : LaurentSeries k) ∈ A :=
    hA ((r⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hg : algebraMap (LaurentSeries k) Ω (g : LaurentSeries k) ∈ A := hA s
  have hg' : algebraMap (LaurentSeries k) Ω ((g⁻¹ : (LaurentSeries k)ˣ) : LaurentSeries k) ∈ A :=
    hA ((s⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) (a ^ m) := by
    change residue A ⟨_, hA (r : k⟦X⟧)⟩ = _
    rw [residue_powerSeries A hk hkres hA hX, hr]
    rfl
  have hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) (b ^ m) := by
    change residue A ⟨_, hA (s : k⟦X⟧)⟩ = _
    rw [residue_powerSeries A hk hkres hA hX, hs]
    rfl
  exact CoreDecompositionBridge.principal_eq_of_reduced_comparison_and_bound A hk hkres
    (rational_residues A hk hkres hA hX) v m n hm hn f g a b hf hf' hg hg'
    hfa hgb hbound hcompare

end CoreLaurentPoint

#print axioms CoreLaurentPoint.constants_compatible
#print axioms CoreLaurentPoint.constantsAlgebra
#print axioms CoreLaurentPoint.constantsSMul
#print axioms CoreLaurentPoint.coefficientAlgebra
#print axioms CoreLaurentPoint.coefficientTower
#print axioms CoreLaurentPoint.residue_powerSeries
#print axioms CoreLaurentPoint.comap_eq_powerSeries_valuationSubring
#print axioms CoreLaurentPoint.rational_residues
#print axioms CoreLaurentPoint.decompositionMap_surjective_at_germ
#print axioms CoreLaurentPoint.principal_eq_of_powerSeries_comparison
