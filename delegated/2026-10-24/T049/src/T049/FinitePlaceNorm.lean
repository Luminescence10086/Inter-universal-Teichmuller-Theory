/-
New work written for handoff task T049 (batch 2026-10-24); no main-line source is
copied or modified. The main-line `core-kummer` package is consumed through its
already-built, read-only `.olean` files (see `lakefile.lean` and `replay.ps1`).

Task T049: wire Mathlib's `FinitePlace.norm_def` to the *actual* local valuation
`CoreFinitePlaceKummer.localValuation` and pin down the exact condition under which
"norm < 1" forces a non-zero integer exponent.

Design constraint from the task card: the base field is a number field `K` and the
local field is a genuine finite-place completion
`fieldAt w = w.maximalIdeal.adicCompletion K`. Nothing below assumes `K = ℚ`, that
the ramification index is one, or that the residue field is `𝔽_p`. Every statement is
quantitative in the *place norm* `c = #(𝓞 K / w) : ℝ≥0`, a rational prime power `> 1`
(`T049.placeNorm`, `T049.one_lt_placeNorm`), and the sharp statement is the two-sided
equivalence `‖x‖ < 1 ↔ exponent v x < 0`.

Sign convention, checked against the source and *not* assumed:
`WithZero.log` is the additive logarithm of the multiplicative value, so for an
element of the maximal ideal (`v x < 1`) the exponent is **negative**. In particular
`‖x‖ < 1` corresponds to `exponent < 0`, not to `0 < exponent`. The docstrings below
state the direction explicitly because the task card's phrase "non-zero exponent" is
sign-agnostic and the sign is exactly the thing that is easy to get wrong.
-/

import Boundary.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Finite-place norms and non-zero exponents

## Main results

* `T049.norm_eq_toNNReal_localValuation`: `FinitePlace.norm_def` restated for the
  actual `CoreFinitePlaceKummer.localValuation`, with the place norm exposed.
* `T049.norm_eq_exp`: the bridge, `‖x‖ = c ^ exponent v x` for `x ≠ 0`.
* `T049.norm_eq_one_iff_exponent_eq_zero`: `‖x‖ = 1 ↔ exponent v x = 0`.
* `T049.norm_lt_one_iff_exponent_neg`: `‖x‖ < 1 ↔ exponent v x < 0` (both directions;
  this is the sharp form, not merely an implication).
* `T049.exponent_ne_zero_of_norm_lt_one`: the literal task target, `‖x‖ < 1` gives
  `exponent v x ≠ 0`.
* `T049.norm_le_one_iff_mem_adicIntegers`: `‖x‖ ≤ 1 ↔ x ∈ w.maximalIdeal.adicCompletionIntegers K`.
* `T049.mem_maximalIdeal_iff_norm_lt_one`: on the actual integer ring (as a
  `valuationSubring`, which is definitionally `adicCompletionIntegers`), membership in
  its maximal ideal is *equivalent* to norm `< 1`.
* `T049.norm_le_one_exponent_eq_zero_unit`: the accurate boundary of the result — the
  weaker hypothesis `‖x‖ ≤ 1` does **not** force a non-zero exponent, witnessed by the
  unit `1`. This is why the report does not claim the `≤ 1` version.
-/

set_option autoImplicit false

noncomputable section

open scoped WithZero Pointwise NNReal
open NumberField IsDedekindDomain KummerTheory CoreDiscreteKummer CoreFinitePlaceKummer

namespace T049

variable {K : Type*} [Field K] [NumberField K]

/-- The place norm `c = #(𝓞 K / w) : ℝ≥0`. This is the base of the exponent in
`FinitePlace.norm_def`, where it is called `e`. It is *not* assumed to be prime, so
nothing here specialises to the `p` of a `ℚ_p`-only treatment. -/
def placeNorm (w : FinitePlace K) : ℝ≥0 :=
  (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ≥0)

theorem one_lt_placeNorm (w : FinitePlace K) : 1 < placeNorm w :=
  HeightOneSpectrum.one_lt_absNorm_nnreal w.maximalIdeal

theorem placeNorm_ne_zero (w : FinitePlace K) : placeNorm w ≠ 0 :=
  HeightOneSpectrum.absNorm_ne_zero w.maximalIdeal

/-- The same base viewed in `ℝ`, where the norm actually lives. -/
theorem one_lt_placeNorm_coe (w : FinitePlace K) : (1 : ℝ) < (placeNorm w : ℝ) := by
  exact_mod_cast one_lt_placeNorm w

theorem placeNorm_coe_pos (w : FinitePlace K) : (0 : ℝ) < (placeNorm w : ℝ) :=
  zero_lt_one.trans (one_lt_placeNorm_coe w)

theorem placeNorm_coe_ne_one (w : FinitePlace K) : (placeNorm w : ℝ) ≠ 1 :=
  (one_lt_placeNorm_coe w).ne'

/-- `localValuation` is a genuine `ℤᵐ⁰`-valued valuation, so its value at a non-zero
element is non-zero. This is what lets us leave the `if x = 0` branch of `toNNReal`. -/
theorem localValuation_ne_zero (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) :
    localValuation w x ≠ 0 :=
  (Valuation.ne_zero_iff (localValuation w)).mpr hx

/-- The wiring step: Mathlib's `FinitePlace.norm_def` states
`‖x‖ = toNNReal _ (Valued.v x)`, and here `Valued.v` is definitionally
`CoreFinitePlaceKummer.localValuation w`. Nothing else is needed to connect them. -/
theorem norm_eq_toNNReal_localValuation (w : FinitePlace K) (x : fieldAt w) :
    ‖x‖ = WithZeroMulInt.toNNReal (placeNorm_ne_zero w) (localValuation w x) :=
  FinitePlace.norm_def (K := K) (R := 𝓞 K) (v := w.maximalIdeal) x

/-- **The bridge.** On non-zero elements the norm is the place norm raised to the
integer exponent of the local valuation. -/
theorem norm_eq_exp (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) :
    ‖x‖ = placeNorm w ^ exponent (localValuation w) x := by
  rw [norm_eq_toNNReal_localValuation w x,
    WithZeroMulInt.toNNReal_neg_apply (placeNorm_ne_zero w) (localValuation_ne_zero w hx),
    WithZero.toAdd_unzero_eq_log]
  rfl

/-- `‖x‖ = 1` exactly when the exponent vanishes. Holds at *every* finite place of
every number field: no hypothesis on `K`, on `w`, or on ramification. -/
theorem norm_eq_one_iff_exponent_eq_zero (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) :
    ‖x‖ = 1 ↔ exponent (localValuation w) x = 0 := by
  rw [norm_eq_exp w hx]
  exact zpow_eq_one_iff_right₀ (placeNorm_coe_pos w).le (placeNorm_coe_ne_one w)

/-- **Sharp form of the task's question.** With `c > 1`, `c ^ e < 1` iff `e < 0`.
Both directions are proved. Note the sign: the exponent of an element with norm `< 1`
is *negative*, since `exponent = WithZero.log (v x)` and `v x < 1`. -/
theorem norm_lt_one_iff_exponent_neg (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) :
    ‖x‖ < 1 ↔ exponent (localValuation w) x < 0 := by
  rw [norm_eq_exp w hx]
  exact zpow_lt_one_iff_right₀ (one_lt_placeNorm_coe w)

/-- Dual form: `‖x‖ ≤ 1` iff the exponent is `≤ 0`, i.e. iff `x` is integral. -/
theorem norm_le_one_iff_exponent_nonpos (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) :
    ‖x‖ ≤ 1 ↔ exponent (localValuation w) x ≤ 0 := by
  rw [norm_eq_exp w hx]
  exact zpow_le_one_iff_right₀ (one_lt_placeNorm_coe w)

/-- **The literal task target**: `‖x‖ < 1` forces a non-zero (in fact negative)
exponent. -/
theorem exponent_ne_zero_of_norm_lt_one (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0)
    (h : ‖x‖ < 1) : exponent (localValuation w) x ≠ 0 :=
  ((norm_lt_one_iff_exponent_neg w hx).mp h).ne

/-- The norm of a non-zero element is positive. -/
theorem norm_pos (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0) : 0 < ‖x‖ := by
  rw [norm_eq_exp w hx]
  exact zpow_pos (placeNorm_coe_pos w) _

/-- Norm `≤ 1` is exactly integrality at the place: membership in the *actual*
`adicCompletionIntegers`, which is by definition the valuation subring
(`CoreFinitePlaceKummer.integerRegion_eq`). -/
theorem norm_le_one_iff_mem_adicIntegers (w : FinitePlace K) (x : fieldAt w) :
    ‖x‖ ≤ 1 ↔ x ∈ (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) := by
  rw [← integerRegion_eq w]
  show ‖x‖ ≤ 1 ↔ x ∈ (localValuation w).valuationSubring
  rw [Valuation.mem_valuationSubring_iff,
    show ‖x‖ = ((WithZeroMulInt.toNNReal (placeNorm_ne_zero w) (localValuation w x) : ℝ≥0) : ℝ)
      from norm_eq_toNNReal_localValuation w x]
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff (one_lt_placeNorm w))

/-- Downstream corollary: integral elements have norm `≤ 1`. -/
theorem norm_le_one_of_mem_adicIntegers (w : FinitePlace K) {x : fieldAt w}
    (h : x ∈ (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w))) : ‖x‖ ≤ 1 :=
  (norm_le_one_iff_mem_adicIntegers w x).mpr h

/-- On the actual integer ring, the maximal ideal is exactly the norm `< 1` locus.
This identifies the norm condition with a purely algebraic one, and it is the form
that a Kummer-theoretic consumer wants (valuation `> 0` ⇒ principal ideal is proper). -/
theorem mem_maximalIdeal_iff_norm_lt_one (w : FinitePlace K)
    (a : (localValuation w).valuationSubring) :
    a ∈ IsLocalRing.maximalIdeal ((localValuation w).valuationSubring) ↔
      ‖(a : fieldAt w)‖ < 1 := by
  rw [Valuation.mem_maximalIdeal_iff,
    norm_eq_toNNReal_localValuation w (a : fieldAt w),
    show (1 : ℝ) = ((1 : ℝ≥0) : ℝ) from rfl, NNReal.coe_lt_coe]
  exact WithZeroMulInt.toNNReal_lt_one_iff (one_lt_placeNorm w)

/-- **The accurate boundary of the result.** The cheaper hypothesis `‖x‖ ≤ 1` is not
enough: the unit `1` satisfies it while its exponent is `0`. Hence no statement of the
shape "norm `≤ 1` ⇒ non-zero exponent" is claimed anywhere in this delivery, and the
strict inequality in the task target cannot be relaxed. -/
theorem norm_le_one_exponent_eq_zero_unit (w : FinitePlace K) :
    ‖(1 : fieldAt w)‖ ≤ 1 ∧ exponent (localValuation w) (1 : fieldAt w) = 0 := by
  have h1 : exponent (localValuation w) (1 : fieldAt w) = 0 := by
    rw [exponent, map_one, WithZero.log_one]
  refine ⟨?_, h1⟩
  rw [norm_eq_exp w one_ne_zero, h1, zpow_zero]

end T049

/-! ## Axiom audit -/

#print axioms T049.placeNorm
#print axioms T049.one_lt_placeNorm
#print axioms T049.placeNorm_ne_zero
#print axioms T049.localValuation_ne_zero
#print axioms T049.norm_eq_toNNReal_localValuation
#print axioms T049.norm_eq_exp
#print axioms T049.norm_eq_one_iff_exponent_eq_zero
#print axioms T049.norm_lt_one_iff_exponent_neg
#print axioms T049.norm_le_one_iff_exponent_nonpos
#print axioms T049.exponent_ne_zero_of_norm_lt_one
#print axioms T049.norm_pos
#print axioms T049.norm_le_one_iff_mem_adicIntegers
#print axioms T049.norm_le_one_of_mem_adicIntegers
#print axioms T049.mem_maximalIdeal_iff_norm_lt_one
#print axioms T049.norm_le_one_exponent_eq_zero_unit
