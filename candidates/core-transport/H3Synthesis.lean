/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W10: the H3 synthesis of (M-i) and (M-ii) — one homomorphic reading, one non-torsion probe

**This file is the synthesis of the two toys `DivideBackTwist.lean` (W8, item M-i) and
`ExponentUniqueness.lean` (W9, item M-ii), and nothing more.** Both toys compute on `ℚ_[3]` with the
reading `CoreTransport.localLog`, and both of their conclusions rest on exactly two facts and on
nothing else:

* **additivity** — the reading of a product is the sum of the readings
  (`PadicLogVolume.padicLog_mul`, read through `localLog_eq_padicLog`, in the toys);
* **non-torsion of the probe** — the probe's own reading is not zero (`norm_localLog_four`,
  `log4_ne_zero` for the probe `4` in the toys).

Nothing further is used in either toy: no root of unity is excluded, no logarithm is inverted, and no
single convergence estimate of the `p`-adic series enters (the estimates in the toys only serve to
*obtain* `localLog 4 ≠ 0`). This file asks what those two facts give **by themselves**, in a setting
where the reading is a homomorphism from a group to the additive group of `ℚ_[3]` and the `p`-adic
analysis is entirely absent.

## Scope: what is proved here

Abstract results (an arbitrary commutative group `G` and an arbitrary reading `R`):

* `reading_pow` — `reading R (x ^ M) = M • reading R x`: the reading is `ℕ`-linear in the exponent.
  Both toys' power laws (`localLog_pow_eq_smul`, hence `reading_pow_four`) are this statement with the
  `p`-adic logarithm in place of `reading R`.
* `exponent_unique` — at a probe whose reading is non-zero, equal readings of the `M`-th and the
  `N`-th powers force `M = N`. This is (M-ii) abstractly: **the exponent is determined exactly when
  the probe has non-zero reading**. W9's `power_reading_injective_on_probe` is the case
  `x = 4`, `reading = localLog`.
* `twist_free_iff` — the twist `u` contributes nothing to any reading, i.e. `∀ x, reading R (u * x) =
  reading R x`, exactly when `reading R u = 0`. This is (M-i)'s condition "the twist term vanishes"
  turned into an `iff`; W8's `twist_insensitive_iff` is the analogous statement with the twist
  residue `localLog u` in place of `reading R u`.
* `divideBack_abstract` — dividing the reading of the twisted `M`-th power by the scalar `M` leaves
  the twist's own reading visible: `reading R (u * x ^ M) / M = reading R u / M + reading R x`. This
  is W8's `divideBack_twist` with `localLog` replaced by an arbitrary additive reading, and with the
  residue `localLog u` replaced by `reading R u`.
* `comparison_well_defined` — **the divide-back conclusion** of (M-i): twist-free (`reading R u = 0`)
  is enough to get the probe's reading back from the divide-back of the twisted `M`-th power. The
  probe condition `reading R x ≠ 0` is **not** an hypothesis of this statement — it belongs to
  `exponent_unique`, which is the (M-ii) half. (An earlier version carried it unused and silenced the
  linter; the hypothesis was dropped instead.)

Degeneracy, in both directions. To keep the numbers literal and the file free of `p`-adic analysis,
the witnesses live in the free commutative group `Multiplicative ℤ` on one generator (its
multiplication is the addition of `ℤ`, so `ofAdd 1` is a genuine non-identity element and `ofAdd n`
is "the twist whose reading is `n`"):

* `exponent_unique_fails_at_zero_reading` — at a probe that is *not* the identity but whose reading is
  zero, two different exponents give the same reading. The hypothesis of `exponent_unique` is
  load-bearing, and the failure is not an artefact of the unit `1`: `zero_reading_powers_agree` gives
  the abstract version, for an arbitrary zero-reading probe.
* `comparison_fails_at_four` — at the twist `4`, the probe `1` and `M = 2` — the same numbers as
  W8's `divideBack_twist_four_one` — the hypothesis `reading R u = 0` is false (`reading_twistFour_ne_zero`)
  and the conclusion of `comparison_well_defined` is **false**: the divide-back reads `4 / 2 = 2`,
  while the probe's reading is `0`.

## The encoding of the reading, and why it is this one

The intended object is a homomorphism from the multiplicative group `G` to the *additive* group of
`ℚ_[3]`, i.e. a map with `R (x * y) = R x + R y`. An `AddMonoidHom` cannot be used directly: the type
`G →+ H` demands an `AddMonoid` structure on `G`, while `G` here carries only a `CommGroup`. The
reading is therefore encoded as a **monoid** homomorphism `R : G →* Multiplicative ℚ_[3]`, whose
multiplication *is* the addition of `ℚ_[3]`, and `reading R` is its additive shadow,
`reading R x = (R x).toAdd`. This is not a weakening: by Mathlib's `MonoidHom.toAdditiveLeft`, such an
`R` is literally the same thing as an additive monoid homomorphism `Additive G →+ ℚ_[3]`
(`reading_eq_toAdditiveLeft`), and the additivity used everywhere below,
`reading R (x * y) = reading R x + reading R y` (`reading_mul`), is `Multiplicative.toAdd_mul`
transported along `map_mul`. Nothing else about the encoding is used, and no statement below mentions
`Multiplicative` except this shadow. (`CommGroup` is kept, as in the task and as in the toys' groups,
although no proof below uses commutativity: `map_mul`, `pow_succ` and `mul_one` suffice.)

## What this file does not say

It does **not** say that any object of the theory carries such a reading. `ℚ_[3]` is the `p`-adic
field, not a log-volume; `x ↦ x ^ M` is not `det^{⊗M}`; `reading R` is neither `localLog` nor a
log-volume of any arithmetic line bundle. No tensor-power Frobenius, log-shell, prime-strip,
Θ-link, Hodge theater, `Ism`, or Corollary 3.12 appears, and no audited `external/iut` interface is
touched. In particular the degeneracy witnesses do **not** exhibit a zero-reading probe "in the
source's fiber", and the twist `4` of `comparison_fails_at_four` is an element of the free group whose
reading is the integer `4`, not W8's `4 ∈ ℚ_[3]` whose reading is `localLog 4` (W8 proves
`‖localLog 4‖ = 1/3`; that estimate is *not* redone here, and it is not the point of the witness). The
load-bearing hypothesis in that witness is `reading R u ≠ 0`, which holds in the toys for `u = 4` and
holds here for the integer `4` alike. Nothing here is evidence for or against any claim of the
source.

The abstraction is honest in the following precise sense: it isolates the two facts the two toys
actually use — additivity of the reading, and non-vanishing of the probe's reading — and derives from
them exactly what those two facts imply. It therefore says **what W8 and W9 share**, and it does not
say that anything in IUT supplies such an `R`, nor that the source's assertions about tensor-power
twists and the exponent `M` are true: those remain open, as recorded in
`research/core-backward-2026-10-23/m-i-design.md` and `m-ii-design.md`.
-/

namespace H3Synthesis

noncomputable section

variable {G : Type*} [CommGroup G]

/-! ## 1. The reading: a group homomorphism written additively -/

/-- **The additive shadow of a reading.** For `R : G →* Multiplicative ℚ_[3]` — a homomorphism from
the multiplicative group `G` into the multiplicative copy of the *additive* group `ℚ_[3]` — the
reading of `x` is the element of `ℚ_[3]` it names: `reading R x = (R x).toAdd`. By
`reading_eq_toAdditiveLeft` this is the same function as `MonoidHom.toAdditiveLeft R` on
`Additive.ofMul x`, so it is an additive monoid homomorphism `Additive G →+ ℚ_[3]` in disguise. -/
def reading (R : G →* Multiplicative ℚ_[3]) (x : G) : ℚ_[3] :=
  Multiplicative.toAdd (R x)

/-- **`reading R` is the additive homomorphism attached to `R`.** Mathlib's
`MonoidHom.toAdditiveLeft` turns a monoid homomorphism `G →* Multiplicative ℚ_[3]` into an additive
monoid homomorphism `Additive G →+ ℚ_[3]`; this theorem records that `reading R` is that
homomorphism, composed with `Additive.ofMul`. It is the reason the encoding `G →* Multiplicative
ℚ_[3]` loses nothing with respect to the intended `G →+ ℚ_[3]`. -/
theorem reading_eq_toAdditiveLeft (R : G →* Multiplicative ℚ_[3]) (x : G) :
    reading R x = MonoidHom.toAdditiveLeft R (Additive.ofMul x) := rfl

/-- **Additivity of the reading.** The reading of a product is the sum of the readings; this is the
one property of the two toys' `localLog` that their computations actually use
(`PadicLogVolume.padicLog_mul` for W8/W9). -/
theorem reading_mul (R : G →* Multiplicative ℚ_[3]) (x y : G) :
    reading R (x * y) = reading R x + reading R y := by
  simp [reading]

/-- **The reading of the identity is zero**, so a unit reading nothing may serve as the "no twist"
element of `twist_free_iff`. -/
theorem reading_one (R : G →* Multiplicative ℚ_[3]) : reading R (1 : G) = 0 := by
  simp [reading]

/-! ## 2. The reading is `ℕ`-linear in the exponent, and pins the exponent when non-zero -/

/-- **The reading of the `M`-th power is `M` times the reading.** Proved from additivity
(`reading_mul`) by induction on `M`; no hypothesis on `M` is needed, and the case `M = 0` holds
because the reading of the identity is zero. This is the abstract form of the toys' power law
`localLog_pow_eq_smul`, hence of W9's `reading_pow_four`. -/
theorem reading_pow (R : G →* Multiplicative ℚ_[3]) (x : G) (M : ℕ) :
    reading R (x ^ M) = M • reading R x := by
  induction M with
  | zero => simp [reading_one]
  | succ M ih => rw [pow_succ, reading_mul, ih, succ_nsmul]

/-- **(M-ii) abstractly: a probe with non-zero reading determines the exponent.** If the probe `x` has
`reading R x ≠ 0`, then two powers of `x` have the same reading exactly when the exponents agree.

* Forward: `reading_pow` turns the hypothesis into `M • reading R x = N • reading R x`, i.e.
  `(M : ℚ_[3]) * reading R x = (N : ℚ_[3]) * reading R x`; the non-zero element `reading R x` is
  cancellable in the field `ℚ_[3]` (`mul_right_cancel₀`), and `Nat.cast_injective` concludes `M = N`.
* Backward: congruence.

This is W9's `power_reading_injective_on_probe` with the probe `4` and the reading `localLog`
replaced by an arbitrary probe and an arbitrary additive reading. The hypothesis `reading R x ≠ 0` is
exactly the non-torsion condition: it is what makes the cancellation available, and
`exponent_unique_fails_at_zero_reading` shows it cannot be dropped. -/
theorem exponent_unique (R : G →* Multiplicative ℚ_[3]) (x : G) (hx : reading R x ≠ 0) {M N : ℕ} :
    reading R (x ^ M) = reading R (x ^ N) ↔ M = N := by
  rw [reading_pow, reading_pow]
  constructor
  · intro h
    rw [nsmul_eq_mul, nsmul_eq_mul] at h
    exact Nat.cast_injective (R := ℚ_[3]) (mul_right_cancel₀ hx h)
  · intro h
    rw [h]

/-! ## 3. (M-i): the twist term vanishes exactly when the twist reads zero -/

/-- **(M-i)'s vanishing condition, as an `iff`.** A twist `u` contributes nothing to the reading of
any product — `∀ x, reading R (u * x) = reading R x` — exactly when its own reading is zero.

* Forward: additivity and `reading R u = 0` give `0 + reading R x = reading R x`.
* Backward: instantiate the insensitivity at `x = 1`; then `reading R (u * 1) = reading R 1 = 0`, and
  `reading R (u * 1) = reading R u`.

This is W8's `twist_insensitive_iff` with `localLog` generalised to an additive reading, and with the
twist's residue `localLog u` generalised to `reading R u`. -/
theorem twist_free_iff (R : G →* Multiplicative ℚ_[3]) (u : G) :
    reading R u = 0 ↔ ∀ x : G, reading R (u * x) = reading R x := by
  constructor
  · intro h x
    rw [reading_mul, h, zero_add]
  · intro h
    simpa [reading_one] using h 1

/-- **(M-i) abstractly: the divide-back, with the twist term visible.** Dividing the reading of the
twisted `M`-th power `u * x ^ M` by the scalar `M` gives the twist's own reading divided by `M`, plus
the reading of `x` — the twist term is not removed by the divide-back. The hypothesis `M ≠ 0` is
exactly what the division needs (`Nat.cast_ne_zero`).

This is W8's `divideBack_twist` (`localLog ((u * x) ^ M) / M = localLog u + localLog x`) with the
`p`-adic logarithm replaced by an arbitrary additive reading; the summand `reading R u / M` is the
abstract counterpart of W8's `twistResidue u`. -/
theorem divideBack_abstract (R : G →* Multiplicative ℚ_[3]) (u x : G) (M : ℕ) (hM : M ≠ 0) :
    reading R (u * x ^ M) / (M : ℚ_[3]) = reading R u / (M : ℚ_[3]) + reading R x := by
  have hM' : (M : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.mpr hM
  rw [reading_mul, reading_pow, nsmul_eq_mul, add_div, mul_div_cancel_left₀ (reading R x) hM']

/-- **The divide-back conclusion.** If the twist reads zero (`reading R u = 0`, the twist-free condition
of `twist_free_iff`), then the divide-back of the twisted `M`-th power *is* the reading of the probe: the
twist term is absent, so dividing by `M` is harmless.

This is the (M-i) half of the synthesis and it is stated **without** the probe hypothesis, because the
identity does not need it — the previous version carried `reading R x ≠ 0` as an unused hypothesis and
silenced the linter; that is fixed here by dropping the hypothesis instead of the warning. The (M-ii)
half, that the surviving reading determines `M`, is `exponent_unique`, which is where the probe condition
actually belongs. -/
theorem comparison_well_defined (R : G →* Multiplicative ℚ_[3]) (u x : G) (hu : reading R u = 0)
    (M : ℕ) (hM : M ≠ 0) :
    reading R (u * x ^ M) / (M : ℚ_[3]) = reading R x := by
  rw [divideBack_abstract R u x M hM, hu, zero_div, zero_add]

/-! ## 4. Degeneracy: the two hypotheses are load-bearing

The witnesses below live in the free commutative group `Multiplicative ℤ` on one generator, whose
multiplication is the addition of `ℤ`. This keeps every number literal and keeps the file free of
`p`-adic analysis: the reading of `ofAdd n` is the integer `n`, cast into `ℚ_[3]`. -/

/-- **The trivial reading on the free group**: every element reads `0`. Its kernel is everything, so
no probe whatsoever is non-torsion for it. -/
def trivialReading : Multiplicative ℤ →* Multiplicative ℚ_[3] where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by
    intro a b
    simp

/-- **The free reading**: the generator `ofAdd 1` reads `1`, so `ofAdd n` reads the integer `n` cast
into `ℚ_[3]`. It is `Int.castAddHom ℚ_[3]` transported to multiplicative notation by Mathlib's
`AddMonoidHom.toMultiplicative`, i.e. an honest additive homomorphism out of `Multiplicative ℤ`. -/
def freeReading : Multiplicative ℤ →* Multiplicative ℚ_[3] :=
  (Int.castAddHom ℚ_[3]).toMultiplicative

/-- The probe of the first degeneracy witness: the generator of the free group. -/
def probeOne : Multiplicative ℤ := Multiplicative.ofAdd 1

/-- The twist of the second degeneracy witness: the free-group element named `4`, i.e. the fourth
power of the generator. Its reading is the integer `4`. -/
def twistFour : Multiplicative ℤ := Multiplicative.ofAdd 4

/-- The free reading computes: `ofAdd n` reads `n`. -/
theorem reading_freeReading (n : ℤ) :
    reading freeReading (Multiplicative.ofAdd n) = (n : ℚ_[3]) := by
  simp [reading, freeReading]

/-- The probe of the first witness is **not** the identity: `ofAdd 1 ≠ ofAdd 0`. This is what makes
the first degeneracy a statement about a non-identity probe with zero reading, rather than about the
unit. -/
theorem probeOne_ne_one : probeOne ≠ 1 := by
  intro h
  have h' : (1 : ℤ) = 0 := by
    simpa [probeOne] using congrArg Multiplicative.toAdd h
  exact one_ne_zero h'

/-- The probe of the first witness reads zero under the trivial reading. -/
theorem zeroReading_probeOne : reading trivialReading probeOne = 0 := by
  simp [reading, trivialReading, probeOne]

/-- **Abstract degeneracy of (M-ii): a probe with zero reading determines nothing.** If
`reading R x = 0`, then the readings of the `M`-th and the `N`-th powers of `x` agree for *every*
pair of exponents, with no hypothesis relating them. So the non-vanishing hypothesis of
`exponent_unique` is not a convenience: on the zero-reading part of `G` the conclusion fails for all
`M ≠ N`. -/
theorem zero_reading_powers_agree (R : G →* Multiplicative ℚ_[3]) (x : G) (hx : reading R x = 0)
    (M N : ℕ) : reading R (x ^ M) = reading R (x ^ N) := by
  simp [reading_pow, hx]

/-- **Degeneracy of (M-ii), with numbers: the non-identity probe `ofAdd 1` under the trivial reading
gives the same reading at the exponents `0` and `1`.** The statement bundles the four facts that make
it a genuine counterexample to the conclusion of `exponent_unique` without its hypothesis: the probe
is not the identity, its reading is zero, the readings of the two powers agree, and the exponents
differ. So `exponent_unique` genuinely fails once its hypothesis is dropped. -/
theorem exponent_unique_fails_at_zero_reading :
    probeOne ≠ 1 ∧ reading trivialReading probeOne = 0 ∧
      reading trivialReading (probeOne ^ 0) = reading trivialReading (probeOne ^ 1) ∧
        (0 : ℕ) ≠ 1 :=
  ⟨probeOne_ne_one, zeroReading_probeOne,
    zero_reading_powers_agree trivialReading probeOne zeroReading_probeOne 0 1, by norm_num⟩

/-- The twist of the second witness reads `4`. -/
theorem reading_twistFour : reading freeReading twistFour = 4 := by
  rw [twistFour, reading_freeReading]
  norm_num

/-- **The twist of the second witness has non-zero reading**: `reading R u ≠ 0`, so the hypothesis
`hu` (the twist-free hypothesis) of `comparison_well_defined` is false at these numbers. -/
theorem reading_twistFour_ne_zero : reading freeReading twistFour ≠ 0 := by
  rw [reading_twistFour]
  exact Nat.cast_ne_zero.mpr (by norm_num)

/-- **Degeneracy of (M-i), with W8's numbers.** At the twist `4`, the probe `1` and `M = 2` — the
numbers of W8's `divideBack_twist_four_one` — the twist has non-zero reading, and then the conclusion
of `comparison_well_defined` is *false*: the divide-back reads `4 / 2 = 2`, while the probe's reading
is `0`. So the hypothesis `reading R u = 0` is load-bearing, and "divide back by `M`" alone does not
remove the twist term.

The inequality is stated as an inequality of the two readings, as required: the left side is the
divide-back of the twisted second power, the right side is the reading of the probe. -/
theorem comparison_fails_at_four :
    reading freeReading (twistFour * (1 : Multiplicative ℤ) ^ 2) / ((2 : ℕ) : ℚ_[3]) ≠
      reading freeReading (1 : Multiplicative ℤ) := by
  have h2 : ((2 : ℕ) : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
  have h42 : (4 : ℚ_[3]) / ((2 : ℕ) : ℚ_[3]) = ((2 : ℕ) : ℚ_[3]) := by
    rw [show (4 : ℚ_[3]) = ((2 : ℕ) : ℚ_[3]) * ((2 : ℕ) : ℚ_[3]) by norm_num]
    exact mul_div_cancel_left₀ ((2 : ℕ) : ℚ_[3]) h2
  rw [divideBack_abstract freeReading twistFour 1 2 (by norm_num), reading_twistFour, reading_one,
    add_zero, h42]
  exact h2

end

end H3Synthesis

#print axioms H3Synthesis.reading
#print axioms H3Synthesis.reading_eq_toAdditiveLeft
#print axioms H3Synthesis.reading_mul
#print axioms H3Synthesis.reading_one
#print axioms H3Synthesis.reading_pow
#print axioms H3Synthesis.exponent_unique
#print axioms H3Synthesis.twist_free_iff
#print axioms H3Synthesis.divideBack_abstract
#print axioms H3Synthesis.comparison_well_defined
#print axioms H3Synthesis.trivialReading
#print axioms H3Synthesis.freeReading
#print axioms H3Synthesis.probeOne
#print axioms H3Synthesis.twistFour
#print axioms H3Synthesis.reading_freeReading
#print axioms H3Synthesis.probeOne_ne_one
#print axioms H3Synthesis.zeroReading_probeOne
#print axioms H3Synthesis.zero_reading_powers_agree
#print axioms H3Synthesis.exponent_unique_fails_at_zero_reading
#print axioms H3Synthesis.reading_twistFour
#print axioms H3Synthesis.reading_twistFour_ne_zero
#print axioms H3Synthesis.comparison_fails_at_four
