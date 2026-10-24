import IntegralMatrixCharacter
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! From preservation of ONE fixed full lattice to an actual integral inverse.
No determinant norm condition is an input. This is a local matrix realization,
not yet an identification of the original IUT allowed operations. -/
set_option autoImplicit false

namespace CoreLatticeStabilizer
open Matrix CoreIntegralMatrix
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {n : Type} [Fintype n] [DecidableEq n]

def standardLattice : Set (n → ℚ_[p]) := {x | ∀ i, ‖x i‖ ≤ 1}

theorem entries_integral_of_mapsTo (A : Matrix n n ℚ_[p])
    (h : Set.MapsTo A.mulVec standardLattice standardLattice) :
    ∀ i j, ‖A i j‖ ≤ 1 := by
  intro i j
  have he : Pi.single j (1 : ℚ_[p]) ∈ (standardLattice : Set (n → ℚ_[p])) := by
    intro k
    by_cases hk : k = j <;> simp [hk]
  have hc := h he
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hc i

def integralLift (A : Matrix n n ℚ_[p]) (h : ∀ i j, ‖A i j‖ ≤ 1) : Matrix n n ℤ_[p] :=
  fun i j => ⟨A i j, h i j⟩

omit [Fintype n] [DecidableEq n] in
theorem extend_integralLift (A : Matrix n n ℚ_[p]) (h : ∀ i j, ‖A i j‖ ≤ 1) :
    extend (integralLift A h) = A := rfl

omit [Fintype n] [DecidableEq n] in
theorem extend_injective : Function.Injective (extend (p := p) (n := n)) := by
  intro A B h
  ext i j
  apply Subtype.ext
  exact congrArg (fun M : Matrix n n ℚ_[p] => M i j) h

omit [DecidableEq n] in
theorem extend_mul (A B : Matrix n n ℤ_[p]) : extend (A * B) = extend A * extend B :=
  Matrix.map_mul

omit [Fintype n] in
@[simp] theorem extend_one : extend (1 : Matrix n n ℤ_[p]) = 1 := by
  simp [extend]

def action (U : (Matrix n n ℚ_[p])ˣ) : (n → ℚ_[p]) → (n → ℚ_[p]) :=
  (U : Matrix n n ℚ_[p]).mulVec

theorem inverse_preserves_of_image (U : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' standardLattice = standardLattice) :
    Set.MapsTo (action (U⁻¹)) standardLattice standardLattice := by
  intro x hx
  rw [← h] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hc : action (U⁻¹) x = y := by
    rw [← hxy]
    change (↑(U⁻¹) : Matrix n n ℚ_[p]) *ᵥ ((U : Matrix n n ℚ_[p]) *ᵥ y) = y
    have hui : (↑(U⁻¹) : Matrix n n ℚ_[p]) * (U : Matrix n n ℚ_[p]) = 1 := U.inv_val
    rw [Matrix.mulVec_mulVec, hui, Matrix.one_mulVec]
  rwa [hc]

/-- Both integral matrices, including the inverse, are constructed from
preservation of the lattice as a set. No inverse-integrality hypothesis is hidden. -/
def integralStabilizer (U : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' standardLattice = standardLattice) : (Matrix n n ℤ_[p])ˣ where
  val := integralLift (U : Matrix n n ℚ_[p]) (entries_integral_of_mapsTo _ (by
    intro x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩))
  inv := integralLift (↑(U⁻¹) : Matrix n n ℚ_[p])
    (entries_integral_of_mapsTo _ (inverse_preserves_of_image U h))
  val_inv := by
    apply extend_injective
    rw [extend_mul, extend_integralLift, extend_integralLift, extend_one]
    exact U.val_inv
  inv_val := by
    apply extend_injective
    rw [extend_mul, extend_integralLift, extend_integralLift, extend_one]
    exact U.inv_val

theorem integralStabilizer_extends (U : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' standardLattice = standardLattice) :
    extend (integralStabilizer U h : Matrix n n ℤ_[p]) = (U : Matrix n n ℚ_[p]) := rfl

/-- Determinant character vanishes as a CONSEQUENCE of same-lattice preservation. -/
theorem determinant_norm_of_stabilizes (U : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' standardLattice = standardLattice) : ‖(U : Matrix n n ℚ_[p]).det‖ = 1 := by
  have hn := integral_automorphism_det_norm (integralStabilizer U h)
  rwa [integralStabilizer_extends] at hn

/-- One-sided preservation gives only a determinant inequality, not equality. -/
theorem determinant_norm_le_of_mapsTo (A : Matrix n n ℚ_[p])
    (h : Set.MapsTo A.mulVec standardLattice standardLattice) : ‖A.det‖ ≤ 1 := by
  let B := integralLift A (entries_integral_of_mapsTo A h)
  have hb : extend B = A := rfl
  rw [← hb, det_extend, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one _

theorem action_mul (U V : (Matrix n n ℚ_[p])ˣ) : action (U * V) = action U ∘ action V := by
  funext x
  exact (Matrix.mulVec_mulVec x (U : Matrix n n ℚ_[p]) (V : Matrix n n ℚ_[p])).symm

theorem action_one : action (1 : (Matrix n n ℚ_[p])ˣ) = id := by
  funext x
  exact Matrix.one_mulVec x

theorem inverse_image_image (B : (Matrix n n ℚ_[p])ˣ) (S : Set (n → ℚ_[p])) :
    action (B⁻¹) '' (action B '' S) = S := by
  rw [← Set.image_comp, ← action_mul, inv_mul_cancel, action_one, Set.image_id]

/-- A full lattice presented in arbitrary coordinates, retaining the actual frame B. -/
def frameLattice (B : (Matrix n n ℚ_[p])ˣ) : Set (n → ℚ_[p]) :=
  action B '' standardLattice

theorem conjugate_stabilizes_standard (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) :
    action (B⁻¹ * U * B) '' standardLattice = standardLattice := by
  calc
    action (B⁻¹ * U * B) '' standardLattice =
        action (B⁻¹) '' (action U '' (action B '' standardLattice)) := by
      rw [action_mul, Set.image_comp, action_mul, Set.image_comp]
    _ = action (B⁻¹) '' (action B '' standardLattice) := by
      change action (B⁻¹) '' (action U '' frameLattice B) = action (B⁻¹) '' frameLattice B
      rw [h]
    _ = standardLattice := inverse_image_image B _

theorem det_conjugate (U B : (Matrix n n ℚ_[p])ˣ) :
    (↑(B⁻¹ * U * B) : Matrix n n ℚ_[p]).det = (U : Matrix n n ℚ_[p]).det := by
  have hb : (↑(B⁻¹) : Matrix n n ℚ_[p]).det * (B : Matrix n n ℚ_[p]).det = 1 := by
    have hi : (↑(B⁻¹) : Matrix n n ℚ_[p]) * (B : Matrix n n ℚ_[p]) = 1 := B.inv_val
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hi
  change ((↑(B⁻¹) : Matrix n n ℚ_[p]) * (U : Matrix n n ℚ_[p]) *
    (B : Matrix n n ℚ_[p])).det = _
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((↑(B⁻¹) : Matrix n n ℚ_[p]).det * (B : Matrix n n ℚ_[p]).det) *
        (U : Matrix n n ℚ_[p]).det := by ring
    _ = _ := by rw [hb, one_mul]

/-- Coordinates need not identify the lattice with the standard one. The
determinant character is still one after an arbitrary fixed change of frame. -/
theorem determinant_norm_of_frame_stabilizes (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) : ‖(U : Matrix n n ℚ_[p]).det‖ = 1 := by
  have hn := determinant_norm_of_stabilizes (B⁻¹ * U * B) (conjugate_stabilizes_standard U B h)
  rwa [det_conjugate] at hn

theorem zero_real_character_of_frame_stabilizes (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) :
    Real.log ‖(U : Matrix n n ℚ_[p]).det‖ = 0 := by
  rw [determinant_norm_of_frame_stabilizes U B h, Real.log_one]

end
end CoreLatticeStabilizer

#print axioms CoreLatticeStabilizer.entries_integral_of_mapsTo
#print axioms CoreLatticeStabilizer.inverse_preserves_of_image
#print axioms CoreLatticeStabilizer.integralStabilizer
#print axioms CoreLatticeStabilizer.integralStabilizer_extends
#print axioms CoreLatticeStabilizer.determinant_norm_of_stabilizes
#print axioms CoreLatticeStabilizer.determinant_norm_le_of_mapsTo
#print axioms CoreLatticeStabilizer.conjugate_stabilizes_standard
#print axioms CoreLatticeStabilizer.det_conjugate
#print axioms CoreLatticeStabilizer.determinant_norm_of_frame_stabilizes
#print axioms CoreLatticeStabilizer.zero_real_character_of_frame_stabilizes
