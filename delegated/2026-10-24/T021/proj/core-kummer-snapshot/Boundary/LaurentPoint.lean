import Boundary.DecompositionBridge
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.KrullDimension.PID

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
