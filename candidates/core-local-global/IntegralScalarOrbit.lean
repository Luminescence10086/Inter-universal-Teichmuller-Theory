import NativeFiber
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-! A concrete rank-one LOCAL model: nonzero scalar contractions of a fixed
unit ball. Over a nonarchimedean field these are multiplications by nonzero
integral scalars on the trivial rank-one integral module. This is NOT a full
local Frobenioid, a global collection, or a construction of the IUT quotient.

Unlike a category allowing every invertible field scalar as an automorphism,
this category forces automorphism norm one from its actual inverse laws.
The logarithm used here is the REAL logarithm of the norm, not the p-adic log. -/
set_option autoImplicit false

namespace CoreIntegralOrbit
open CategoryTheory CoreLocalGlobal
noncomputable section
variable (K : Type) [NormedField K]

def integralNonzero : Submonoid K where
  carrier := {a | a ≠ 0 ∧ ‖a‖ ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, hna⟩ ⟨hb, hnb⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hna (norm_nonneg b)).trans (by simpa using hnb)

abbrev Scalar := ↥(integralNonzero K)
abbrev LocalCat := SingleObj (Scalar K)
abbrev point : LocalCat K := SingleObj.star _

variable {K}

def scalarValue (f : Scalar K) : K := f.val

/-- The norm-one property of an actual automorphism is DERIVED, not a field. -/
theorem automorphism_norm_one (e : point K ≅ point K) :
    ‖scalarValue e.hom‖ = 1 := by
  have hu : ‖scalarValue e.hom‖ ≤ 1 := e.hom.property.2
  have hv : ‖scalarValue e.inv‖ ≤ 1 := e.inv.property.2
  have he : scalarValue e.inv * scalarValue e.hom = 1 :=
    congrArg scalarValue e.hom_inv_id
  have hn : ‖scalarValue e.inv‖ * ‖scalarValue e.hom‖ = 1 := by
    rw [← norm_mul, he, norm_one]
  have hle := mul_le_mul_of_nonneg_right hv (norm_nonneg (scalarValue e.hom))
  rw [hn, one_mul] at hle
  exact le_antisymm hu hle

def normOneIso (a : K) (ha : a ≠ 0) (hn : ‖a‖ = 1) : point K ≅ point K where
  hom := ⟨a, ha, hn.le⟩
  inv := ⟨a⁻¹, inv_ne_zero ha, by simp [norm_inv, hn]⟩
  hom_inv_id := by apply Subtype.ext; exact inv_mul_cancel₀ ha
  inv_hom_id := by apply Subtype.ext; exact mul_inv_cancel₀ ha

/-- Complete classification of target-automorphism orbits in this rank-one model. -/
theorem orbit_eq_iff_norm_eq (f g : Scalar K) :
    Quotient.mk (targetOrbit (point K) (point K)) f = Quotient.mk _ g ↔
      ‖(f : K)‖ = ‖(g : K)‖ := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Quotient.exact h
    have hc : scalarValue e.hom * (f : K) = (g : K) :=
      congrArg (fun k : Scalar K => (k : K)) he
    have hn := congrArg norm hc
    rw [norm_mul, automorphism_norm_one, one_mul] at hn
    exact hn
  · intro h
    have hf : ‖(f : K)‖ ≠ 0 := norm_ne_zero_iff.mpr f.property.1
    have hn : ‖(g : K) / (f : K)‖ = 1 := by rw [norm_div, ← h, div_self hf]
    let e := normOneIso ((g : K) / (f : K)) (div_ne_zero g.property.1 f.property.1) hn
    apply Quotient.sound
    refine ⟨e, ?_⟩
    apply Subtype.ext
    exact div_mul_cancel₀ (g : K) f.property.1

/-- A well-defined readout on the EXISTING categorical target orbit. -/
def logNormRead : PolyHom (point K) (point K) → ℝ :=
  Quotient.lift (fun f : Scalar K => Real.log ‖(f : K)‖) (by
    intro f g h
    have hn := (orbit_eq_iff_norm_eq f g).mp (Quotient.sound h)
    exact congrArg Real.log hn)

@[simp] theorem logNormRead_mk (f : Scalar K) :
    logNormRead (Quotient.mk _ f) = Real.log ‖(f : K)‖ := rfl

/-- Composition has an exact additive character, after passing to arrow orbits. -/
theorem logNormRead_precomp (f : Scalar K) (p : PolyHom (point K) (point K)) :
    logNormRead (precomp f p) = Real.log ‖(f : K)‖ + logNormRead p := by
  induction p using Quotient.inductionOn with
  | h g =>
    change Real.log ‖scalarValue g * (f : K)‖ = Real.log ‖(f : K)‖ + Real.log ‖scalarValue g‖
    dsimp only [scalarValue]
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr g.property.1)
      (norm_ne_zero_iff.mpr f.property.1)]
    exact add_comm _ _

/-- Effectivity (norm-nonincreasing) yields a sign constraint on the readout. -/
theorem logNormRead_nonpos (p : PolyHom (point K) (point K)) : logNormRead p ≤ 0 := by
  induction p using Quotient.inductionOn with
  | h f => exact Real.log_nonpos (norm_nonneg _) f.property.2

/-- A zero character detects exactly the identity orbit, not arbitrary equality
of the chosen scalar representatives. -/
theorem logNormRead_zero_iff (f : Scalar K) :
    logNormRead (Quotient.mk _ f) = 0 ↔
      Quotient.mk (targetOrbit (point K) (point K)) f = Quotient.mk _ (1 : Scalar K) := by
  rw [orbit_eq_iff_norm_eq, logNormRead_mk]
  change Real.log ‖(f : K)‖ = 0 ↔ ‖(f : K)‖ = ‖(1 : K)‖
  rw [norm_one]
  constructor
  · exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr f.property.1)
  · intro h; rw [h, Real.log_one]

section Q3
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def threeArrow : Scalar ℚ_[3] := ⟨3, by norm_num, by
  have hn : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by simpa using (Padic.norm_p (p := 3))
  rw [hn]
  norm_num⟩

theorem three_read : logNormRead (Quotient.mk _ threeArrow) = -Real.log 3 := by
  rw [logNormRead_mk]
  change Real.log ‖(3 : ℚ_[3])‖ = _
  have hn : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by simpa using (Padic.norm_p (p := 3))
  rw [hn, Real.log_inv]

/-- Uniformizer scaling survives this integral-unit orbit. It is not silently
identified with the identity by allowing all nonzero field automorphisms. -/
theorem three_orbit_not_identity :
    Quotient.mk (targetOrbit (point ℚ_[3]) (point ℚ_[3])) threeArrow ≠
      Quotient.mk _ (1 : Scalar ℚ_[3]) := by
  intro h
  have he := (orbit_eq_iff_norm_eq threeArrow 1).mp h
  change ‖(3 : ℚ_[3])‖ = ‖(1 : ℚ_[3])‖ at he
  have hn : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by simpa using (Padic.norm_p (p := 3))
  rw [hn, norm_one] at he
  norm_num at he

end Q3
end
end CoreIntegralOrbit

#print axioms CoreIntegralOrbit.automorphism_norm_one
#print axioms CoreIntegralOrbit.normOneIso
#print axioms CoreIntegralOrbit.orbit_eq_iff_norm_eq
#print axioms CoreIntegralOrbit.logNormRead
#print axioms CoreIntegralOrbit.logNormRead_precomp
#print axioms CoreIntegralOrbit.logNormRead_nonpos
#print axioms CoreIntegralOrbit.logNormRead_zero_iff
#print axioms CoreIntegralOrbit.three_read
#print axioms CoreIntegralOrbit.three_orbit_not_identity
