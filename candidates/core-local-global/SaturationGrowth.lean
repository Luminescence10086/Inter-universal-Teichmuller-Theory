import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A finite quotient regression for a tempting but invalid use of zero
determinant character: each individual automorphism preserves counting measure,
while taking the union of its images can enlarge a region. This is NOT an IUT
counterexample and does not assert a Haar-measure lifting theorem. -/
set_option autoImplicit false

namespace CoreSaturationGrowth
abbrev Vec := Fin 2 → ZMod 3

def shear : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 0, 1]
def region : Finset Vec := Finset.univ.filter (fun x => x 0 = 0)
def moved : Finset Vec := region.image shear.mulVec

theorem shear_det_one : shear.det = 1 := by decide

theorem shear_bijective : Function.Bijective shear.mulVec := by decide

theorem shear_not_coordinate_ring_linear :
    ¬ ∀ a x : Vec, shear.mulVec (a * x) = a * shear.mulVec x := by decide

theorem region_card : region.card = 3 := by decide
theorem moved_card : moved.card = 3 := by decide
theorem saturated_card : (region ∪ moved).card = 5 := by decide

/-- Individual maps preserve determinant and cardinality, but the union grows. -/
theorem zero_character_does_not_prevent_saturation_growth :
    shear.det = 1 ∧ Function.Bijective shear.mulVec ∧
      region.card = moved.card ∧ region.card < (region ∪ moved).card := by
  exact ⟨shear_det_one, shear_bijective, by rw [region_card, moved_card],
    by rw [region_card, saturated_card]; decide⟩

/-- The original region is already an ideal for the coordinatewise coefficient
ring F_3 × F_3. The shear is linear over F_3, not over this larger ring. -/
def coordinateIdeal : Ideal Vec where
  carrier := {x | x 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x 0 + y 0 = 0
    rw [hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change a 0 * x 0 = 0
    rw [hx, mul_zero]

theorem region_as_ideal : (region : Set Vec) = (coordinateIdeal : Set Vec) := by
  ext x
  simp [region, coordinateIdeal]

theorem span_region : Ideal.span (region : Set Vec) = coordinateIdeal := by
  rw [region_as_ideal, Ideal.span_eq]

theorem one_mem_moved : (1 : Vec) ∈ moved := by decide

/-- Closing the moved region under the larger coordinate ring produces the
whole space. This finite ideal hull is an analogy, not IUT's holomorphic hull. -/
theorem span_moved_eq_top : Ideal.span (moved : Set Vec) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  exact Ideal.subset_span one_mem_moved

theorem whole_card : (Finset.univ : Finset Vec).card = 9 := by decide

/-- A nonzero finite counting-log correction remains despite determinant one.
No identification with a p-adic Haar-volume correction is asserted here. -/
theorem finite_hull_log_gain :
    Real.log ((Finset.univ : Finset Vec).card : ℝ) - Real.log (region.card : ℝ) =
      Real.log 3 := by
  rw [whole_card, region_card]
  change Real.log 9 - Real.log 3 = Real.log 3
  rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, Real.log_pow]
  ring

end CoreSaturationGrowth

#print axioms CoreSaturationGrowth.shear_det_one
#print axioms CoreSaturationGrowth.shear_bijective
#print axioms CoreSaturationGrowth.shear_not_coordinate_ring_linear
#print axioms CoreSaturationGrowth.region_card
#print axioms CoreSaturationGrowth.moved_card
#print axioms CoreSaturationGrowth.saturated_card
#print axioms CoreSaturationGrowth.zero_character_does_not_prevent_saturation_growth
#print axioms CoreSaturationGrowth.region_as_ideal
#print axioms CoreSaturationGrowth.span_region
#print axioms CoreSaturationGrowth.one_mem_moved
#print axioms CoreSaturationGrowth.span_moved_eq_top
#print axioms CoreSaturationGrowth.whole_card
#print axioms CoreSaturationGrowth.finite_hull_log_gain
