import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-! Finite-dimensional normalization calculation motivated by IUT III,
Remark 3.1.1(iv) and Remark 3.9.5(vii), Ob3/Ob4.

Matrices encode chosen frames, not an IUT hull. The reference frame is retained.
No identification with Haar volume, Arakelov degree, a formal quotient, or the
original legal-output family is asserted. Positive powers below are powers of
the scalar on the determinant LINE, not Kronecker powers of the vector space. -/
set_option autoImplicit false

namespace CoreNormalization
noncomputable section
open Matrix
open scoped Kronecker

variable {K : Type*} [NormedField K]

/-- A nonzero scalar's additive norm reading. Used only with explicit nonzero
hypotheses for multiplication; `Real.log 0` must not make singular frames legal. -/
def logNorm (a : K) : ℝ := Real.log ‖a‖

theorem logNorm_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    logNorm (a * b) = logNorm a + logNorm b := by
  simp only [logNorm, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)

theorem logNorm_pow (a : K) (M : ℕ) :
    logNorm (a ^ M) = (M : ℝ) * logNorm a := by
  simp only [logNorm, norm_pow, Real.log_pow]

theorem logNorm_div {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    logNorm (a / b) = logNorm a - logNorm b := by
  simp only [logNorm, norm_div]
  exact Real.log_div (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Relative determinant reading of a frame against an explicit reference.
The minus sign on the reference implements the inverse determinant in Ob3-1-2. -/
def relativeLogDet (A A₀ : Matrix m m K) : ℝ := logNorm A.det - logNorm A₀.det

theorem relativeLogDet_eq_ratio {A A₀ : Matrix m m K}
    (hA : A.det ≠ 0) (hA₀ : A₀.det ≠ 0) :
    relativeLogDet A A₀ = logNorm (A.det / A₀.det) :=
  (logNorm_div hA hA₀).symm

/-- A common change of ambient coordinates cancels, even when its determinant
norm is not one. The reference must undergo the SAME coordinate change. -/
theorem relativeLogDet_common_left {A A₀ U : Matrix m m K}
    (hA : A.det ≠ 0) (hA₀ : A₀.det ≠ 0) (hU : U.det ≠ 0) :
    relativeLogDet (U * A) (U * A₀) = relativeLogDet A A₀ := by
  simp only [relativeLogDet, Matrix.det_mul, logNorm_mul hU hA,
    logNorm_mul hU hA₀]
  ring

/-- A defect acting on the output frame alone contributes its own determinant
character. It cannot be cancelled by rebasing the reference independently. -/
theorem relativeLogDet_left_defect {A A₀ D : Matrix m m K}
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) :
    relativeLogDet (D * A) A₀ = logNorm D.det + relativeLogDet A A₀ := by
  rw [relativeLogDet, Matrix.det_mul, logNorm_mul hD hA, relativeLogDet]
  ring

/-- The exact condition for a matrix representative defect to be numerically
invisible is unit determinant norm, which is weaker than the defect being identity. -/
theorem relativeLogDet_defect_invariant_iff {A A₀ D : Matrix m m K}
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) :
    relativeLogDet (D * A) A₀ = relativeLogDet A A₀ ↔ ‖D.det‖ = 1 := by
  rw [relativeLogDet_left_defect hA hD]
  constructor
  · intro h
    have hz : logNorm D.det = 0 := by linarith
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr hD) hz
  · intro h
    simp [logNorm, h]

/-- Scalar dilation relative to the same reference frame has no residual
reference determinant. This computes the determinant-line exponent explicitly. -/
theorem relativeLogDet_scalar {A₀ : Matrix m m K} {a : K}
    (hA₀ : A₀.det ≠ 0) (ha : a ≠ 0) :
    relativeLogDet (a • A₀) A₀ = (Fintype.card m : ℝ) * logNorm a := by
  rw [relativeLogDet, Matrix.det_smul,
    logNorm_mul (pow_ne_zero _ ha) hA₀, logNorm_pow]
  ring

/-- Exact determinant exponents of the two-factor tensor packet. -/
theorem relativeLogDet_kronecker {A A₀ : Matrix m m K} {B B₀ : Matrix n n K}
    (hA : A.det ≠ 0) (hA₀ : A₀.det ≠ 0)
    (hB : B.det ≠ 0) (hB₀ : B₀.det ≠ 0) :
    relativeLogDet (A ⊗ₖ B) (A₀ ⊗ₖ B₀) =
      (Fintype.card n : ℝ) * relativeLogDet A A₀ +
      (Fintype.card m : ℝ) * relativeLogDet B B₀ := by
  simp only [relativeLogDet, Matrix.det_kronecker,
    logNorm_mul (pow_ne_zero _ hA) (pow_ne_zero _ hB),
    logNorm_mul (pow_ne_zero _ hA₀) (pow_ne_zero _ hB₀), logNorm_pow]
  ring

/-- Dividing by the packet dimension yields reciprocal-dimension weights,
with no assumption that either reference determinant is one. -/
theorem normalized_kronecker [Nonempty m] [Nonempty n]
    {A A₀ : Matrix m m K} {B B₀ : Matrix n n K}
    (hA : A.det ≠ 0) (hA₀ : A₀.det ≠ 0)
    (hB : B.det ≠ 0) (hB₀ : B₀.det ≠ 0) :
    relativeLogDet (A ⊗ₖ B) (A₀ ⊗ₖ B₀) /
        ((Fintype.card m : ℝ) * (Fintype.card n : ℝ)) =
      relativeLogDet A A₀ / (Fintype.card m : ℝ) +
      relativeLogDet B B₀ / (Fintype.card n : ℝ) := by
  rw [relativeLogDet_kronecker hA hA₀ hB hB₀]
  have hm : (Fintype.card m : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The scalar on the relative determinant line after a positive tensor power. -/
def poweredRead (M : ℕ) (A A₀ : Matrix m m K) : ℝ :=
  logNorm ((A.det / A₀.det) ^ M) / (M : ℝ)

/-- Uniform in M: computing a numerical M is unnecessary for this cancellation. -/
theorem poweredRead_eq {M : ℕ} (hM : 0 < M) {A A₀ : Matrix m m K}
    (hA : A.det ≠ 0) (hA₀ : A₀.det ≠ 0) :
    poweredRead M A A₀ = relativeLogDet A A₀ := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  rw [poweredRead, logNorm_pow, logNorm_div hA hA₀]
  exact mul_div_cancel_left₀ _ hm

/-- A genuine torsion scalar has zero additive norm reading. This does not
assert that every original stack-theoretic twist is such a scalar. -/
theorem torsion_logNorm_zero {t : K} {M : ℕ} (hM : 0 < M) (ht : t ^ M = 1) :
    logNorm t = 0 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have h := logNorm_pow t M
  rw [ht] at h
  simp only [logNorm, norm_one, Real.log_one] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hm

/-- Tensor-power roots related by actual torsion give the same scalar reading. -/
theorem torsion_twist_invariant {a t : K} {M : ℕ}
    (ha : a ≠ 0) (ht : t ≠ 0) (hM : 0 < M) (hpow : t ^ M = 1) :
    logNorm (t * a) = logNorm a := by
  rw [logNorm_mul ht ha, torsion_logNorm_zero hM hpow, zero_add]

/-- Positive-power readings determine the unpowered reading, without selecting
a root. Equality of powered scalars suffices; root existence is not assumed. -/
theorem logNorm_eq_of_pow_eq {a b : K} {M : ℕ}
    (hM : 0 < M) (h : a ^ M = b ^ M) : logNorm a = logNorm b := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have he := congrArg (logNorm (K := K)) h
  rw [logNorm_pow, logNorm_pow] at he
  exact mul_left_cancel₀ hm he

section WeightedPacket
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The product weight of Remark 3.1.1(iv), kept separate from the determinant
tensor exponent M of Ob3. Equality of those original constructions is not assumed. -/
def packetSize (N : V → ℕ) : ℕ := ∏ v, N v

def packetWeight (N : V → ℕ) (v : V) : ℕ :=
  ∏ w ∈ Finset.univ.erase v, N w

theorem packetWeight_mul (N : V → ℕ) (v : V) :
    packetWeight N v * N v = packetSize N := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ v)

/-- Tensor product of one-dimensional determinant characters, repeated with
the indicated integer weights. r_v may be a relative determinant ratio. -/
def weightedDet (N : V → ℕ) (r : V → K) : K :=
  ∏ v, r v ^ packetWeight N v

theorem logNorm_prod (r : V → K) (hr : ∀ v, r v ≠ 0) :
    logNorm (∏ v, r v) = ∑ v, logNorm (r v) := by
  have h : ∀ s : Finset V, logNorm (∏ v ∈ s, r v) = ∑ v ∈ s, logNorm (r v) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [logNorm]
    | @insert v s hv ih =>
      rw [Finset.prod_insert hv, Finset.sum_insert hv,
        logNorm_mul (hr v) (Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)), ih]
  exact h Finset.univ

/-- Exact scalar character counterpart of the E-weighted product-region formula.
No identification of r_v with the original region's measure is a premise or conclusion. -/
theorem weightedDet_normalized (N : V → ℕ) (hN : ∀ v, 0 < N v)
    (r : V → K) (hr : ∀ v, r v ≠ 0) :
    logNorm (weightedDet N r) / (packetSize N : ℝ) =
      ∑ v, logNorm (r v) / (N v : ℝ) := by
  have hsize : (packetSize N : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr (fun v _ => Nat.ne_of_gt (hN v)))
  rw [weightedDet, logNorm_prod _ (fun v => pow_ne_zero _ (hr v))]
  simp_rw [logNorm_pow]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hv : (N v : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hN v)
  have hw : (packetWeight N v : ℝ) * (N v : ℝ) = (packetSize N : ℝ) := by
    exact_mod_cast packetWeight_mul N v
  apply (div_eq_div_iff hsize hv).mpr
  calc
    (packetWeight N v : ℝ) * logNorm (r v) * (N v : ℝ) =
        logNorm (r v) * ((packetWeight N v : ℝ) * (N v : ℝ)) := by ring
    _ = _ := by rw [hw]

/-- An extra positive tensor power cancels AFTER weighting as well: the two
normalizations commute. The result is uniform in the additional exponent T. -/
theorem weightedDet_power_normalized (N : V → ℕ) (hN : ∀ v, 0 < N v)
    (r : V → K) (hr : ∀ v, r v ≠ 0) {T : ℕ} (hT : 0 < T) :
    logNorm (weightedDet N r ^ T) / ((T : ℝ) * (packetSize N : ℝ)) =
      ∑ v, logNorm (r v) / (N v : ℝ) := by
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  rw [logNorm_pow, mul_div_mul_left _ _ ht]
  exact weightedDet_normalized N hN r hr

end WeightedPacket

section SectionConvention

/-- Coefficient ball a O (for a nonarchimedean field this is a principal
fractional lattice). We do not claim a lattice structure over every NormedField. -/
def coefficientBall (a : K) : Set K := {x | ‖x‖ ≤ ‖a‖}

/-- If the chosen section has local norm ‖a‖, the coefficient x of x s must
satisfy ‖x a‖ ≤ 1. This is the convention in the external ArithLineBundle API. -/
def sectionUnitBall (a : K) : Set K := {x | ‖x * a‖ ≤ 1}

/-- The inverse in the section-to-lattice convention is derived from the norm
condition; it is not chosen to fit the desired degree comparison. -/
theorem sectionUnitBall_eq_inverse {a : K} (ha : a ≠ 0) :
    sectionUnitBall a = coefficientBall a⁻¹ := by
  ext x
  change ‖x * a‖ ≤ 1 ↔ ‖x‖ ≤ ‖a⁻¹‖
  rw [norm_mul, norm_inv, ← one_div, le_div_iff₀ (norm_pos_iff.mpr ha)]

theorem inverse_logNorm (a : K) : logNorm a⁻¹ = -logNorm a := by
  simp only [logNorm, norm_inv, Real.log_inv]

end SectionConvention

section ActualQ3
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem q3_norm_three : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by
  simpa using (Padic.norm_p (p := 3))

/-- An actual local field calibration: q O and the unit ball for section datum
q have opposite log radii. It does not identify either with the original hull. -/
theorem q3_sign_calibration :
    logNorm (3 : ℚ_[3]) = -Real.log 3 ∧
      logNorm (3 : ℚ_[3])⁻¹ = Real.log 3 := by
  have h : logNorm (3 : ℚ_[3]) = -Real.log 3 := by
    rw [logNorm, q3_norm_three, Real.log_inv]
  exact ⟨h, by rw [inverse_logNorm, h, neg_neg]⟩

/-- The two balls are observably different: 1 lies in the section's unit ball
but not in 3 O. The witness prevents silently conflating the conventions. -/
theorem q3_balls_different :
    (1 : ℚ_[3]) ∈ sectionUnitBall (3 : ℚ_[3]) ∧
      (1 : ℚ_[3]) ∉ coefficientBall (3 : ℚ_[3]) := by
  constructor
  · change ‖(1 : ℚ_[3]) * 3‖ ≤ 1
    rw [one_mul, q3_norm_three]
    norm_num
  · change ¬ ‖(1 : ℚ_[3])‖ ≤ ‖(3 : ℚ_[3])‖
    rw [norm_one, q3_norm_three]
    norm_num

end ActualQ3

end
end CoreNormalization

#print axioms CoreNormalization.relativeLogDet_common_left
#print axioms CoreNormalization.relativeLogDet_left_defect
#print axioms CoreNormalization.relativeLogDet_defect_invariant_iff
#print axioms CoreNormalization.relativeLogDet_kronecker
#print axioms CoreNormalization.normalized_kronecker
#print axioms CoreNormalization.poweredRead_eq
#print axioms CoreNormalization.torsion_logNorm_zero
#print axioms CoreNormalization.torsion_twist_invariant
#print axioms CoreNormalization.logNorm_eq_of_pow_eq
#print axioms CoreNormalization.packetWeight_mul
#print axioms CoreNormalization.weightedDet_normalized
#print axioms CoreNormalization.weightedDet_power_normalized
#print axioms CoreNormalization.relativeLogDet_scalar
#print axioms CoreNormalization.sectionUnitBall_eq_inverse
#print axioms CoreNormalization.q3_sign_calibration
#print axioms CoreNormalization.q3_balls_different
