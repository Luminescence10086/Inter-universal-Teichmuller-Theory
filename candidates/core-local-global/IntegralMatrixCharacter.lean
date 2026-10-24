import IntegralScalarOrbit
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Actual integral matrix automorphisms, rather than an assumed norm-one
determinant certificate. This constructs the determinant character on GL_n(Z_p)
and its functor to the rank-one integral-scalar category. A source IUT ambiguity
has NOT been shown to be such an integral lattice automorphism. -/
set_option autoImplicit false

namespace CoreIntegralMatrix
open CategoryTheory CoreIntegralOrbit
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {n : Type} [Fintype n] [DecidableEq n]

def extend (A : Matrix n n ℤ_[p]) : Matrix n n ℚ_[p] :=
  A.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])

theorem det_extend (A : Matrix n n ℤ_[p]) :
    (extend A).det = ((A.det : ℤ_[p]) : ℚ_[p]) :=
  ((PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).map_det A).symm

/-- Integral inverse laws imply a unit determinant; Mathlib's actual Z_p norm
then gives norm one. No determinant norm condition is supplied as an assumption. -/
theorem integral_automorphism_det_norm (U : (Matrix n n ℤ_[p])ˣ) :
    ‖(extend (U : Matrix n n ℤ_[p])).det‖ = 1 := by
  rw [det_extend, ← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.mp (U.isUnit.map Matrix.detMonoidHom)

def determinantCharacter : (Matrix n n ℤ_[p])ˣ →* Scalar ℚ_[p] where
  toFun U := ⟨(extend (U : Matrix n n ℤ_[p])).det,
    norm_ne_zero_iff.mp (by rw [integral_automorphism_det_norm U]; exact one_ne_zero),
    (integral_automorphism_det_norm U).le⟩
  map_one' := by
    apply Subtype.ext
    simp [det_extend]
  map_mul' U V := by
    apply Subtype.ext
    simp [det_extend, Matrix.det_mul]

/-- A concrete representation from integral matrix changes of frame to
rank-one determinant arrows, with composition proved by the determinant law. -/
def determinantFunctor : SingleObj ((Matrix n n ℤ_[p])ˣ) ⥤ LocalCat ℚ_[p] :=
  determinantCharacter.toFunctor

theorem determinantCharacter_norm (U : (Matrix n n ℤ_[p])ˣ) :
    ‖scalarValue (determinantCharacter U)‖ = 1 :=
  integral_automorphism_det_norm U

/-- Actual integral matrix automorphisms have zero determinant readout in the
existing scalar orbit. This is a constructed instance of the earlier zero-character route. -/
theorem determinantCharacter_read_zero (U : (Matrix n n ℤ_[p])ˣ) :
    logNormRead (Quotient.mk (CoreLocalGlobal.targetOrbit (point ℚ_[p]) (point ℚ_[p]))
      (determinantCharacter U)) = 0 := by
  rw [logNormRead_mk]
  change Real.log ‖scalarValue (determinantCharacter U)‖ = 0
  rw [determinantCharacter_norm, Real.log_one]

/-- Changing only the output frame is now harmless because the change has been
constructed as an INTEGRAL automorphism, not an arbitrary field-linear map. -/
theorem integral_left_preserves_det_read (U : (Matrix n n ℤ_[p])ˣ)
    (A : Matrix n n ℚ_[p]) :
    Real.log ‖(extend (U : Matrix n n ℤ_[p]) * A).det‖ = Real.log ‖A.det‖ := by
  rw [Matrix.det_mul, norm_mul, integral_automorphism_det_norm, one_mul]

theorem integral_right_preserves_det_read (U : (Matrix n n ℤ_[p])ˣ)
    (A : Matrix n n ℚ_[p]) :
    Real.log ‖(A * extend (U : Matrix n n ℤ_[p])).det‖ = Real.log ‖A.det‖ := by
  rw [Matrix.det_mul, norm_mul, integral_automorphism_det_norm, mul_one]

end
end CoreIntegralMatrix

#print axioms CoreIntegralMatrix.det_extend
#print axioms CoreIntegralMatrix.integral_automorphism_det_norm
#print axioms CoreIntegralMatrix.determinantFunctor
#print axioms CoreIntegralMatrix.determinantCharacter_norm
#print axioms CoreIntegralMatrix.determinantCharacter_read_zero
#print axioms CoreIntegralMatrix.integral_left_preserves_det_read
#print axioms CoreIntegralMatrix.integral_right_preserves_det_read
