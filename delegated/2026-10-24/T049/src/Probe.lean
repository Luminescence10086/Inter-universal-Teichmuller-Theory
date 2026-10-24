import Boundary.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! Scratch probe: names and instance availability. Not part of the deliverable. -/
set_option autoImplicit false

noncomputable section

namespace T049Probe
open scoped WithZero Pointwise
open NumberField IsDedekindDomain KummerTheory CoreDiscreteKummer

variable {K : Type*} [Field K] [NumberField K]

-- 1. Does the FiniteFree instance set resolve for `𝓞 K`?
example : Module.Finite ℤ (𝓞 K) := inferInstance
example : Module.Free ℤ (𝓞 K) := inferInstance

-- 2. Norm instance on fieldAt w
example (w : FinitePlace K) : NormedField (CoreFinitePlaceKummer.fieldAt w) := inferInstance

-- 3. norm_def specialization
example (w : FinitePlace K) (x : CoreFinitePlaceKummer.fieldAt w) :
    ‖x‖ = WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero w.maximalIdeal)
      (CoreFinitePlaceKummer.localValuation w x) :=
  FinitePlace.norm_def (K := K) (R := 𝓞 K) (v := w.maximalIdeal) x

-- 4. toNNReal_exp name
example {e : ℝ≥0} (he : e ≠ 0) (k : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp k) = e ^ k := by
  rw [WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero k), WithZero.toAdd_unzero_eq_log]

-- 5. toNNReal lt one
example {e : ℝ≥0} (he : 1 < e) {m : ℤᵐ⁰} : WithZeroMulInt.toNNReal he.ne_zero m < 1 ↔ m < 1 :=
  WithZeroMulInt.toNNReal_lt_one_iff he

-- 6. exponent in terms of log, and v x ≠ 0
example (w : FinitePlace K) {x : CoreFinitePlaceKummer.fieldAt w} (hx : x ≠ 0) :
    CoreFinitePlaceKummer.localValuation w x ≠ 0 :=
  (Valuation.ne_zero_iff (CoreFinitePlaceKummer.localValuation w)).mpr hx

example (w : FinitePlace K) {x : CoreFinitePlaceKummer.fieldAt w} (hx : x ≠ 0) :
    WithZero.exp (CoreDiscreteKummer.exponent (CoreFinitePlaceKummer.localValuation w) x)
      = CoreFinitePlaceKummer.localValuation w x :=
  WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)

-- 7. adicCompletionIntegers as valuation subring
example (w : FinitePlace K) :
    CoreDiscreteKummer.integerRegion (CoreFinitePlaceKummer.localValuation w) =
      (w.maximalIdeal.adicCompletionIntegers K : Set (CoreFinitePlaceKummer.fieldAt w)) :=
  CoreFinitePlaceKummer.integerRegion_eq w

end T049Probe
