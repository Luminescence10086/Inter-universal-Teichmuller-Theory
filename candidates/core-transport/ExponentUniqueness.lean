/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W9 toy province: what determines the exponent `M`, and what leaves it undetermined

**This file is a toy province for item (M-ii) of the H3 prerequisites
(`research/core-backward-2026-10-23/h3-prerequisites.md`, §M-ii), and nothing more.** It formalises
one thing and only that thing: *an exponent is pinned down by a probe exactly when the probe's reading
is non-zero.* Both directions are proved here. A probe with non-zero reading determines the exponent
(`power_reading_injective_on_probe`, `exponent_determined`). A probe with zero reading — the unit `1`,
i.e. a torsion probe — determines nothing at all (`not_determined_by_torsion_probe`), and the same
holds for every probe with zero reading, the root-of-unity case included
(`log_eq_zero_of_pow_eq_one`, `not_determined_by_zero_reading`,
`torsion_probe_determines_nothing`).

## What the source says, and what it does not say

(Ob3-2), txt 8084–8101: the `M` in `det^{⊗M}(−)` is "the **[uniquely determined]** positive integer
[cf. the positive integer `N_E` that appears in the final portion of the discussion of Remark 3.1.1,
(iv)] such that this operation maps an arithmetic line bundle to the `M`-th tensor power of the
arithmetic line bundle". Uniqueness is *asserted*; no value is given; and the tie to `N_E` is a bare
"cf.", not an equation. The obligation (M-ii) recorded in `h3-prerequisites.md` is to show that the
`M` of the hull determinant, the `M` of the q-pilot-side `M`-th tensor power, and the degree-`M`
Frobenius of (Ob4-1) are the same `M`.

**The point of this file.** "`M` is the integer such that the operation raises to the `M`-th tensor
power" determines `M` only through a *reading* of that operation, and a reading pins `M` only if it is
**non-zero**. If `localLog (4 ^ M) = localLog (4 ^ N)` for a probe whose reading is non-zero, then
`M = N`: the power law rewrites the two readings as `M * localLog 4` and `N * localLog 4`, and a
non-zero element of a field may be cancelled. At a probe with zero reading — the unit `1`, or any root
of unity — *every* pair `M ≠ N` gives the same reading, so such a probe cannot distinguish exponents
at all.

**This is why (Ob3-2)'s "cf. `N_E`" cannot by itself pin `M`.** The "cf." supplies no probe, and in
particular no probe whose reading is proved non-zero. An identification of the three uses of `M` in
the source needs an object on which the operation's reading is non-zero, exhibited and computed; a
footnote reference to another positive integer is not such an object. The toy shows the shape of what
would be needed, not that the source's three `M`s are or are not the same.

## What is restated rather than imported

`algorithmRun`, `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`,
`localLog_one`, `localLog_pow_eq_smul` are restated with the same statements from W8
(`DivideBackTwist.lean`) and W3 (`DivideBackLaw.lean`); they carry no new mathematics. See the last
section of this docstring for why they cannot be imported.

Proved here, not assumed:

* `norm_logTerm_four_le`, `norm_localLog_four`, `log4_ne_zero` — the probe `4` has **non-zero**
  reading; in fact `‖localLog 4‖ = 1/3`, by the ultrametric domination of the leading term
  `4 - 1 = 3` over the tail. No root-of-unity hypothesis and no appeal to the kernel of the logarithm
  is used;
* `power_reading_injective_on_probe` — on the single probe `4` the reading of the `M`-th power is
  injective in `M`, stated as an `↔` so that non-zero reading gives *exactly* determination;
* `exponent_determined` — the "determined by all probes" version, obtained by specialising to `4`;
* `not_determined_by_torsion_probe` — the reverse direction, which is the point: on the unit `1`
  every exponent gives the same reading;
* `log_eq_zero_of_pow_eq_one`, `not_determined_by_zero_reading`,
  `torsion_probe_determines_nothing` — the same statement for any probe with zero reading.

## What this file does not say

It does **not** identify the source's three `M`s, and it does **not** value `M`. `ℚ_[3]` is a complete
discretely valued field; it is not the localisation of an arithmetic line bundle; `x ↦ x ^ M` is not
`det^{⊗M}`; and `CoreTransport.localLog` is the `p`-adic logarithm, not a log-volume. No probe in the
source's setting is exhibited, and nothing here says that the source's "uniquely determined" is false,
or that its "cf. `N_E`" is unfounded: the toy says only that *this kind of argument* — an asserted
uniqueness plus a bare "cf." — supplies no probe, hence no determination in the toy's sense. The file
also says nothing about the two normalizations of (M-iii), about log-volumes, log-shells,
prime-strips, Θ-links, `Ism`, Hodge theaters, Corollary 3.12, or any audited `external/iut`
interface. Nothing here is evidence for or against any IUT claim.

## Why declarations are restated instead of imported

`candidates/core-transport/lakefile.lean` declares the single library `CoreTransport`, whose modules
are the ones under `CoreTransport/`. `DivideBackTwist.lean` (W8), `DivideBackLaw.lean` (W3) and
`ExecutionProvenance.lean` sit at the top level of the package, so they are not Lake targets, no
`.olean` is produced for them, and they cannot be imported. The declarations this file needs from
them are therefore restated with the same statements. One deliberate difference is retained from W8:
`localLog_pow_eq_smul` is stated **without** the hypothesis `M ≠ 0`, because its upstream source
`PadicLogVolume.padicLog_pow` needs none; the identity does hold at `M = 0` (both sides are `0`, since
`x ^ 0 = 1` and `localLog 1 = 0`).

The `p`-adic mathematics is quoted, not re-proved: `localLog_pow_eq_smul` is
`PadicLogVolume.padicLog_pow` (`candidates/core-log/PadicLogVolume/PadicLog.lean`) read through the
definition-level identification of the two literal series; convergence is
`CoreLog.principal_unit_log_hasSum`; the root-of-unity input to §4 is
`PadicLogVolume.padicLog_eq_zero_of_pow_eq_one`; the arithmetic input to the non-vanishing proof is
`PadicLogVolume.norm_natCast_eq_pow` and `PadicLogVolume.factorization_lt_self`.
-/

namespace ExponentUniqueness

noncomputable section

/-! ## 1. The quoted pieces: the algorithm, the two series, and the power law -/

/-- **The finite algorithm**, with the same statement as `ExecutionProvenance.algorithmRun`: the
`n`-th partial sum of the logarithm series at `x`, with term `(-1)^k (x-1)^(k+1)/(k+1)`. This is the
partial-sum algorithm of the `p`-adic logarithm on `ℚ_[3]`, not the η-algorithm of IUT. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the quoted series term,
definitionally (`rfl`), so `algorithmRun` is the same sequence whose sum
`hasSum_logTerm_localLog` identifies with `CoreTransport.localLog`. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- **Definition-level identification of the two literal series.** `CoreTransport.localLog` and
`PadicLogVolume.padicLog` are the same series, written twice; unfolding both definitions proves it,
so the step carries no mathematical content of its own. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **The existing convergence result, quoted.** For `‖x - 1‖ < 1` the series sums to
`CoreTransport.localLog x`; the proof goes through `CoreLog.principal_unit_log_summable`, hence
through the genuine `p`-adic convergence argument and not through `tsum`'s totalised default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact CoreLog.principal_unit_log_hasSum hx

/-- The reading of the unit: `localLog 1 = 0`. This is `PadicLogVolume.padicLog_one` read through
`localLog_eq_padicLog`; it is the zero reading that makes the torsion probe `1` determine nothing. -/
theorem localLog_one : CoreTransport.localLog (1 : ℚ_[3]) = 0 := by
  rw [localLog_eq_padicLog 1]
  exact PadicLogVolume.padicLog_one

/-- **The reading of the `M`-th power is `M` times the reading.** Derived from
`PadicLogVolume.padicLog_pow` read through `localLog_eq_padicLog` at `x ^ M` and at `x`.

There is **no** hypothesis `M ≠ 0`: upstream `padicLog_pow` needs none, and the identity does hold at
`M = 0` (both sides are `0`, since `x ^ 0 = 1` and `localLog 1 = 0`). This is the law that turns a
comparison of readings of `M`-th and `N`-th powers into a comparison of the scalars `M` and `N`. -/
theorem localLog_pow_eq_smul (x : ℚ_[3]) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    CoreTransport.localLog (x ^ M) = (M : ℚ_[3]) * CoreTransport.localLog x := by
  rw [localLog_eq_padicLog (x ^ M), localLog_eq_padicLog x,
    PadicLogVolume.padicLog_pow (p := 3) (k := ℚ_[3]) (by decide) CoreLog.norm_three_lt_one hx M]

/-! ## 2. The probe at `4` has non-zero reading -/

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`, so the reading may be taken at
the probe `x = 4` and the power law applies there. -/
theorem norm_four_sub_one_Q3 : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- `‖3‖ ^ 2 = 1 / 9` in `ℚ_[3]`: the size of the leading term of the logarithm series at `4`, and
the bound for the whole tail. -/
theorem norm_three_sq_Q3 : ‖(3 : ℚ_[3])‖ ^ 2 = (1 / 9 : ℝ) := by
  rw [CoreLog.norm_three]
  norm_num

/-- **The tail of the logarithm series at `4` is small.** For `n ≥ 1` the `n`-th term has norm at
most `‖3‖ ^ 2 = 1/9`: its norm is `‖3‖ ^ (n + 1) * ‖(n + 1 : ℚ_[3])‖⁻¹ = ‖3‖ ^ (n + 1 - v)` with
`v = v_3(n + 1)`, and `v < n` because `3 ^ v ≤ n + 1 < 3 ^ n` — the estimate `1 + 2 n ≤ 3 ^ n` of
`one_add_mul_le_pow` rules out `v = n`. (No root-of-unity hypothesis is used anywhere here.) -/
theorem norm_logTerm_four_le {n : ℕ} (hn : n ≠ 0) :
    ‖PadicLogVolume.logTerm (4 : ℚ_[3]) n‖ ≤ ‖(3 : ℚ_[3])‖ ^ 2 := by
  have hp : Nat.Prime 3 := by decide
  have h3pos : (0 : ℝ) < ‖(3 : ℚ_[3])‖ := by
    rw [CoreLog.norm_three]
    norm_num
  have hv_lt : (n + 1).factorization 3 < n + 1 :=
    PadicLogVolume.factorization_lt_self hp (Nat.succ_ne_zero n)
  have hv_le : (n + 1).factorization 3 ≤ n := by omega
  have hv_ne : (n + 1).factorization 3 ≠ n := by
    intro hvn
    have hord : 3 ^ (n + 1).factorization 3 ≤ n + 1 :=
      Nat.ordProj_le 3 (Nat.succ_ne_zero n)
    rw [hvn] at hord
    have hz : (1 : ℤ) + (n : ℤ) * 2 ≤ 3 ^ n := by
      have h := one_add_mul_le_pow (a := (2 : ℤ)) (by norm_num) n
      simpa using h
    have hnpos : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hgt : ((n : ℤ) + 1) < 3 ^ n := by nlinarith
    have hgt' : n + 1 < 3 ^ n := by exact_mod_cast hgt
    omega
  have h4 : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [PadicLogVolume.norm_logTerm, h4,
    PadicLogVolume.norm_natCast_eq_pow (p := 3) (k := ℚ_[3]) hp CoreLog.norm_three_lt_one
      (Nat.succ_ne_zero n)]
  calc ‖(3 : ℚ_[3])‖ ^ (n + 1) * (‖(3 : ℚ_[3])‖ ^ (n + 1).factorization 3)⁻¹
      = ‖(3 : ℚ_[3])‖ ^ (n + 1 - (n + 1).factorization 3) := by
        rw [pow_sub₀ ‖(3 : ℚ_[3])‖ h3pos.ne' (by omega)]
    _ ≤ ‖(3 : ℚ_[3])‖ ^ 2 :=
        pow_le_pow_of_le_one (norm_nonneg _) CoreLog.norm_three_lt_one.le (by omega)

/-- **`‖localLog 4‖ = 1/3`.** The leading term of the logarithm series at `4` is `4 - 1 = 3`, of
norm `1/3`, and the whole tail has norm at most `1/9 < 1/3`; by the ultrametric maximum principle the
reading has exactly the size of its leading term. This is proved, not quoted: the split is at the
leading term, and the tail bound is `norm_logTerm_four_le` termwise. -/
theorem norm_localLog_four : ‖CoreTransport.localLog (4 : ℚ_[3])‖ = (1 / 3 : ℝ) := by
  have hsum : Summable (PadicLogVolume.logTerm (4 : ℚ_[3])) :=
    CoreLog.principal_unit_log_summable norm_four_sub_one_Q3
  have htsum : CoreTransport.localLog (4 : ℚ_[3]) =
      ∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) n := by
    rw [localLog_eq_padicLog]
    rfl
  have hsplit : CoreTransport.localLog (4 : ℚ_[3]) =
      ((4 : ℚ_[3]) - 1) + ∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1) := by
    simp only [htsum, Summable.tsum_eq_zero_add hsum, PadicLogVolume.logTerm_zero]
  have hterm : ∀ n : ℕ, ‖PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1)‖ ≤ (1 / 9 : ℝ) := fun n =>
    (norm_logTerm_four_le (Nat.succ_ne_zero n)).trans (le_of_eq norm_three_sq_Q3)
  have htail : ‖∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1)‖ ≤ (1 / 9 : ℝ) :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) hterm
  have hlead : ‖((4 : ℚ_[3]) - 1)‖ = (1 / 3 : ℝ) := by
    have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
    rw [h, CoreLog.norm_three]
    norm_num
  have hne : ‖((4 : ℚ_[3]) - 1)‖ ≠
      ‖∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1)‖ := by
    rw [hlead]
    intro hc
    rw [← hc] at htail
    norm_num at htail
  have hle : ‖∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1)‖ ≤ (1 / 3 : ℝ) :=
    htail.trans (by norm_num)
  calc ‖CoreTransport.localLog (4 : ℚ_[3])‖
      = max ‖((4 : ℚ_[3]) - 1)‖
          ‖∑' n : ℕ, PadicLogVolume.logTerm (4 : ℚ_[3]) (n + 1)‖ := by
        rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
    _ = (1 / 3 : ℝ) := by
        rw [hlead]
        exact max_eq_left hle

/-- **The probe at `4` has non-zero reading**: `localLog 4 ≠ 0`, because its norm is `1/3`. This is
the theorem, not a hypothesis, that makes `power_reading_injective_on_probe` work: a non-zero element
of the field `ℚ_[3]` is cancellable, and that cancellation is exactly what turns a comparison of
readings into a comparison of exponents. -/
theorem log4_ne_zero : CoreTransport.localLog (4 : ℚ_[3]) ≠ 0 := by
  intro h
  have hnorm := norm_localLog_four
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-! ## 3. A probe with non-zero reading determines the exponent -/

/-- **The reading of the `M`-th power at `4`, with the exponent pulled out**: by the power law,
`localLog (4 ^ M) = M * localLog 4`. This is `localLog_pow_eq_smul` specialised to the probe `4`,
whose domain condition is `norm_four_sub_one_Q3`. -/
theorem reading_pow_four (M : ℕ) :
    CoreTransport.localLog ((4 : ℚ_[3]) ^ M) = (M : ℚ_[3]) * CoreTransport.localLog (4 : ℚ_[3]) :=
  localLog_pow_eq_smul (4 : ℚ_[3]) norm_four_sub_one_Q3 M

/-- **The reading of the `M`-th power at the probe `4` is injective in `M`.** The reading
`M ↦ localLog (4 ^ M)` takes the same value at `M` and at `N` exactly when `M = N`.

* Forward: by `reading_pow_four` both sides become `M * localLog 4` and `N * localLog 4`; cancelling
  the **non-zero** field element `localLog 4` (`log4_ne_zero`, via `mul_right_cancel₀`) gives
  `(M : ℚ_[3]) = (N : ℚ_[3])`, and `Nat.cast_injective` gives `M = N`.
* Backward: congruence.

The `↔` is what makes this a statement about *determination* and not merely about consistency: the
probe `4` loses no information about the exponent. The cancellation is available precisely because the
probe's reading is proved non-zero; at a probe with zero reading no such cancellation is possible —
that is §4. -/
theorem power_reading_injective_on_probe (M N : ℕ) :
    CoreTransport.localLog ((4 : ℚ_[3]) ^ M) = CoreTransport.localLog ((4 : ℚ_[3]) ^ N) ↔
      M = N := by
  constructor
  · intro h
    rw [reading_pow_four M, reading_pow_four N] at h
    have hcast : (M : ℚ_[3]) = (N : ℚ_[3]) := mul_right_cancel₀ log4_ne_zero h
    exact Nat.cast_injective (R := ℚ_[3]) hcast
  · intro h
    rw [h]

/-- **The exponent is determined by the readings of all probes.** If for every `x` the readings of
the `M`-th and `N`-th powers agree, then `M = N`. The proof is the specialisation of the hypothesis to
the single probe `x = 4`, where the reading is non-zero (`log4_ne_zero`), followed by
`power_reading_injective_on_probe`.

Note what the hypothesis asks for: *all* probes. The weakness is not in the conclusion but in the
hypothesis — and (Ob3-2) supplies no probe at all, let alone a family of them. -/
theorem exponent_determined (M N : ℕ)
    (h : ∀ x : ℚ_[3], CoreTransport.localLog (x ^ M) = CoreTransport.localLog (x ^ N)) : M = N :=
  (power_reading_injective_on_probe M N).1 (h 4)

/-! ## 4. A probe with zero reading determines nothing: the zero-reading probe -/

/-- **The reverse direction, which is the point: a probe whose reading is zero determines nothing.**
At the unit `1` — whose reading is zero — the readings of the `M`-th and the `N`-th powers agree for
**every** pair of exponents, so a comparison of readings at `1` is compatible with any exponent whatsoever,
and an argument that only ever evaluates the operation at `1` cannot single out a value of `M`.

**This is why (Ob3-2)'s "cf. `N_E`" cannot by itself pin `M`.** (Ob3-2) asserts uniqueness and points,
by a bare "cf.", at another positive integer; it exhibits no probe on which the reading is non-zero.
In the toy, uniqueness of `M` is a theorem on the part of the object where the reading is non-zero
(§3) and is *false* on the part where it vanishes (§4). A "cf." that names no probe therefore
determines nothing, in exactly the sense made precise here. -/
theorem not_determined_by_torsion_probe (M N : ℕ) :
    CoreTransport.localLog ((1 : ℚ_[3]) ^ M) = CoreTransport.localLog ((1 : ℚ_[3]) ^ N) := by
  rw [one_pow, one_pow]

/-- **The witness for the failure, with two different exponents spelled out.** Exponents `0` and `1` are
different yet give the same reading at the probe `1`, which is what "the hypothesis fails" means
concretely. (The previous version carried `M ≠ N` as a hypothesis and therefore never used it; this
one states the two exponents explicitly.) -/
theorem torsion_probe_witness : ∃ M N : ℕ, M ≠ N ∧
    CoreTransport.localLog ((1 : ℚ_[3]) ^ M) = CoreTransport.localLog ((1 : ℚ_[3]) ^ N) :=
  ⟨0, 1, by norm_num, by simp⟩

/-- **Roots of unity among the principal units have zero reading.** If `u ^ n = 1` with `n ≠ 0` and
`‖u - 1‖ < 1`, then `localLog u = 0`, by `PadicLogVolume.padicLog_eq_zero_of_pow_eq_one` read through
`localLog_eq_padicLog`. This is the shape under which the torsion probe `1` generalises: the unit `1`
is the case `n = 1`. -/
theorem log_eq_zero_of_pow_eq_one {u : ℚ_[3]} (hu : ‖u - 1‖ < 1) {n : ℕ} (hn : n ≠ 0)
    (h : u ^ n = 1) : CoreTransport.localLog u = 0 := by
  rw [localLog_eq_padicLog u]
  exact PadicLogVolume.padicLog_eq_zero_of_pow_eq_one (p := 3) (k := ℚ_[3]) (by decide)
    CoreLog.norm_three_lt_one hu hn h

/-- **Every probe with zero reading determines nothing.** If `localLog u = 0` and the power law is
applicable at `u` (`‖u - 1‖ < 1`), then the readings of the `M`-th and `N`-th powers of `u` agree for
all `M`, `N`, with no hypothesis relating them: both readings are `M * 0 = 0` and `N * 0 = 0`. This
is `not_determined_by_torsion_probe` with the probe `1` replaced by an arbitrary zero-reading probe,
and it shows that the failure of determination is a property of the reading's value, not of the
particular element chosen. -/
theorem not_determined_by_zero_reading (u : ℚ_[3]) (hu : ‖u - 1‖ < 1)
    (h0 : CoreTransport.localLog u = 0) (M N : ℕ) :
    CoreTransport.localLog (u ^ M) = CoreTransport.localLog (u ^ N) := by
  rw [localLog_pow_eq_smul u hu M, localLog_pow_eq_smul u hu N, h0, mul_zero, mul_zero]

/-- **A root-of-unity probe determines nothing**, in one statement: for `u ^ n = 1` with `n ≠ 0` and
`‖u - 1‖ < 1`, every pair of exponents gives the same reading. The unit `1` is the case `n = 1`, so
this contains `not_determined_by_torsion_probe`; conversely, no root of unity in the principal units
does better than `1`. -/
theorem torsion_probe_determines_nothing {u : ℚ_[3]} (hu : ‖u - 1‖ < 1) {n : ℕ} (hn : n ≠ 0)
    (h : u ^ n = 1) (M N : ℕ) :
    CoreTransport.localLog (u ^ M) = CoreTransport.localLog (u ^ N) :=
  not_determined_by_zero_reading u hu (log_eq_zero_of_pow_eq_one hu hn h) M N

end

end ExponentUniqueness

#print axioms ExponentUniqueness.algorithmRun
#print axioms ExponentUniqueness.algorithmRun_eq_partialSums
#print axioms ExponentUniqueness.localLog_eq_padicLog
#print axioms ExponentUniqueness.hasSum_logTerm_localLog
#print axioms ExponentUniqueness.localLog_one
#print axioms ExponentUniqueness.localLog_pow_eq_smul
#print axioms ExponentUniqueness.norm_four_sub_one_Q3
#print axioms ExponentUniqueness.norm_three_sq_Q3
#print axioms ExponentUniqueness.norm_logTerm_four_le
#print axioms ExponentUniqueness.norm_localLog_four
#print axioms ExponentUniqueness.log4_ne_zero
#print axioms ExponentUniqueness.reading_pow_four
#print axioms ExponentUniqueness.power_reading_injective_on_probe
#print axioms ExponentUniqueness.exponent_determined
#print axioms ExponentUniqueness.not_determined_by_torsion_probe
#print axioms ExponentUniqueness.torsion_probe_witness
#print axioms ExponentUniqueness.log_eq_zero_of_pow_eq_one
#print axioms ExponentUniqueness.not_determined_by_zero_reading
#print axioms ExponentUniqueness.torsion_probe_determines_nothing
