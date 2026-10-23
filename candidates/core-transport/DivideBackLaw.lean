import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W3 toy province: the `M`-th power is divided back by the logarithm, not by the norm

**This file is a toy province for item 3 of the current goal — the H3 prerequisite of
`research/core-backward-2026-10-23/design-h1-h3.md`, §1′(d) — and nothing more.** It formalises one
shape and only that shape: *a reading that is a logarithm sends the `M`-th power of the object to
`M` times the reading of the object, so dividing back by `M` recovers the original reading; a
reading that is a magnitude instead does not, because dividing by `M` is not what an `M`-th power
does to a magnitude.*

Concretely, on `ℚ_[3]`, with the reading taken on the principal units `‖x - 1‖ < 1`:

* the reading is `CoreTransport.localLog`, the literal logarithm series;
* the stand-in for the "`M`-th tensor power" of the object is the field power `x ^ M`;
* `localLog_pow_eq_smul` and `divide_back` say the reading of `x ^ M` is `M` times the reading of
  `x`, hence the reading of `x` is recovered by dividing by `M`;
* `naive_magnitude_divide_back_fails` says the analogous statement is false for the naive magnitude
  reading `‖·‖`: at `x = 4`, `M = 2` one gets `‖4 ^ 2‖ / 2 = 1 / 2` while `‖4‖ = 1`.

**Why this shape and not the object itself.** `handoffs/core-backward-2026-10-23/M2/` records three
accounting items that the source leaves open (`normalizations.csv` rows M2-07, M2-12, M2-14, M2-25;
`QUESTIONS.md` Q1–Q3, Q5, Q6), and `design-h1-h3.md` §1′(d) carries them into H3:

* **(M-i) there is no divide-back map in the source.** (Ob4), p.133, txt 8135–8144, and (Ob4-3),
  p.134, txt 8185–8189, only *assert* that the confusion between an arithmetic line bundle and its
  `M`-th tensor power is harmless. No map from the `M`-th-power reading to the original reading is
  constructed there, and no bound and no invariance statement is given.
* **(M-ii) `M` is never valued.** (Ob3-2), p.132, txt 8084–8109, characterises `M` only as the
  positive integer with `det^{⊗M}(−)` the `M`-th tensor power, and ties it to `N_E` of
  Remark 3.1.1(iv) by a bare "cf." only.
* **(M-iii) two normalizations are used but never written.** (xi-d), p.183, txt 11022, reads
  `[suitably normalized, with respect to j ∈ |F_l|]` with no formula, while Step (x) uses the
  average over `j ∈ F_l^⋆`; and Proposition 3.9(iii), p.117, txt 7089, identifies the global
  log-volume with an arithmetic degree only `relative to a suitable normalization`.

**What this file does say about them.** Only the *shape* of (M-i), and only on `ℚ_[3]`: if the
reading is a logarithm on the principal units, then "the reading of the `M`-th power is `M` times
the reading of the object" is a theorem (`localLog_pow_eq_smul`), so no separately postulated
divide-back map is needed in that case — division by the scalar `M` does it (`divide_back`). The
toy also exhibits a reading for which exactly this fails
(`naive_magnitude_divide_back_fails`), so the property is not automatic for an arbitrary reading and
"divide by `M`" is not a content-free step.

**What this file does not say.** It does **not** pin the source's `M` (M-ii); it does **not**
construct the divide-back map for the tensor-power Frobenioids of (Ob4-1)/(Ob4-2)/(Ob4-3), and it
proves nothing about the tensor-power twist; it says **nothing** about either normalization of
(M-iii); and it touches none of the log-volume, log-shells, prime-strips, Θ-links, `Ism`, Hodge
theaters, Corollary 3.12, or any object of the audited `external/iut` interfaces. `ℚ_[3]` is a
complete discretely valued field, not the localisation of an arithmetic vector bundle, and
`x ↦ x ^ M` is not `det^{⊗M}`. Nothing here is evidence for or against any IUT claim.

**The `p`-adic mathematics is quoted, not re-proved.** `localLog_pow_eq_smul` is
`PadicLogVolume.padicLog_pow` (`candidates/core-log/PadicLogVolume/PadicLog.lean`) read through the
definition-level identification of the two literal series. One point deserves to be explicit: the
hypothesis `‖x - 1‖ < 1` must hold of *both* `x` and `x ^ M`, otherwise neither side of the law is a
convergent series; that it is preserved under powers is `PadicLogVolume.norm_pow_sub_one_lt`,
re-exported below as `norm_pow_sub_one_lt_Q3`. Convergence itself is not re-proved either; it is
`CoreLog.principal_unit_log_hasSum`.

**Why `algorithmRun` and `hasSum_logTerm_localLog` are repeated here.**
`candidates/core-transport/lakefile.lean` declares a single library, `lean_lib CoreTransport`, whose
modules are the ones under `CoreTransport/`. `ExecutionProvenance.lean` is a top-level module of the
package, so it is not a Lake target: `lake build ExecutionProvenance` fails with
``unknown target `ExecutionProvenance` `` and no `ExecutionProvenance.olean` exists in
`.lake/build/lib/lean`, so it cannot be imported. The declarations are therefore restated with the
same statements rather than imported; they carry no new mathematics.
-/

namespace DivideBackLaw

noncomputable section

/-! ## 1. The toy algorithm and the two literal series -/

/-- **The finite algorithm**, with the same statement as `ExecutionProvenance.algorithmRun`: the
`n`-th partial sum of the logarithm series at `x`, with term `(-1)^k (x-1)^(k+1)/(k+1)`. This is the
partial-sum algorithm of the `p`-adic logarithm on `ℚ_[3]`, not the η-algorithm of IUT. It is a
plain definition, so it is tied to `localLog` by `algorithmRun_eq_partialSums` (`rfl`) rather than by
an assumption. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the quoted series term,
definitionally (`rfl`). This is what keeps `algorithmRun` from being decorative: it is the same
sequence whose sum `hasSum_logTerm_localLog` identifies with `CoreTransport.localLog`. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- **Definition-level identification of the two literal series.** `CoreTransport.localLog` and
`PadicLogVolume.padicLog` are the same series, written twice; unfolding both definitions proves it,
so the step carries no mathematical content of its own. It is repeated here — with its companion
`hasSum_logTerm_localLog` — only because `ExecutionProvenance.lean` is not a Lake target and has no
olean (see the module docstring), so it cannot be imported. -/
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

/-! ## 2. The `M`-th power law, and dividing back by `M` -/

/-- **The domain condition survives powers.** `‖x - 1‖ < 1` implies `‖x ^ M - 1‖ < 1` for every `M`,
so the reading is defined at `x ^ M` as well as at `x`: both sides of the power law below are sums of
a genuinely convergent series. This is `PadicLogVolume.norm_pow_sub_one_lt`, re-exported so that the
preservation is a named fact of this file and not a hidden side condition of the law. -/
theorem norm_pow_sub_one_lt_Q3 (x : ℚ_[3]) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    ‖x ^ M - 1‖ < 1 :=
  PadicLogVolume.norm_pow_sub_one_lt hx M

/-- **Dividing back by `M`.** The reading of `x` is recovered from the reading of its `M`-th power by
dividing by the scalar `M` — the toy stand-in for "divide back the `M`-th tensor power". The
hypothesis `M ≠ 0` is exactly what the division needs, via `Nat.cast_ne_zero`.

This is the primitive step of the file, and it is placed first for that reason: it is the step the
source omits (M-i), and the multiplied form below is recovered *from* it by multiplying by the same
nonzero scalar, not the other way round.

Note what this does *not* say: it is not a map between two Frobenioids, and the scalar `M` here is a
number, not the `M` of (Ob3-2). -/
theorem divide_back (x : ℚ_[3]) (hx : ‖x - 1‖ < 1) (M : ℕ) (hM0 : M ≠ 0) :
    CoreTransport.localLog x = CoreTransport.localLog (x ^ M) / (M : ℚ_[3]) := by
  have h := PadicLogVolume.padicLog_pow (p := 3) (k := ℚ_[3]) (by decide)
    CoreLog.norm_three_lt_one hx M
  rw [localLog_eq_padicLog (x ^ M), localLog_eq_padicLog x, h,
    eq_div_iff (Nat.cast_ne_zero.2 hM0)]
  ring

/-- **The toy law: the reading of the `M`-th power is `M` times the reading.**

Derived from `divide_back` — which is itself `PadicLogVolume.padicLog_pow`, not re-proved, read
through `localLog_eq_padicLog` at `x ^ M` and at `x`. The domain condition is the one preserved by
`norm_pow_sub_one_lt_Q3`.

The hypothesis `hM : M ≠ 0` is used twice here, and it is not removable from the *route*: both
multiplying the divided law back up and cancelling the scalar require `M` to be invertible in
`ℚ_[3]`. The identity itself does hold at `M = 0` (both sides are then `0`, since `x ^ 0 = 1` and
`localLog 1 = 0`), which is why the hypothesis is carried by the interface rather than by the
mathematics. -/
theorem localLog_pow_eq_smul (x : ℚ_[3]) (hx : ‖x - 1‖ < 1) (M : ℕ) (hM : M ≠ 0) :
    CoreTransport.localLog (x ^ M) = (M : ℚ_[3]) * CoreTransport.localLog x := by
  have hM' : (M : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.2 hM
  calc CoreTransport.localLog (x ^ M)
      = (CoreTransport.localLog (x ^ M) / (M : ℚ_[3])) * (M : ℚ_[3]) := by
          rw [div_mul_eq_mul_div, eq_div_iff hM']
    _ = CoreTransport.localLog x * (M : ℚ_[3]) := by rw [← divide_back x hx M hM]
    _ = (M : ℚ_[3]) * CoreTransport.localLog x := mul_comm _ _

/-! ## 3. Anti-degeneracy: the naive magnitude reading has no divide-back

The reading `‖·‖` is the natural competitor to the logarithm: it is also defined on all of
`ℚ_[3]`, it is also a "size". It fails the law, and the failure is concrete — not a negated
universal, and not a statement about a totalised value of a divergent series. -/

/-- **The naive magnitude reading**: the `p`-adic norm of the object. -/
def naiveMagnitude (x : ℚ_[3]) : ℝ := ‖x‖

/-- **Divide back by `M` on the naive magnitude reading**: the magnitude of the `M`-th power, divided
by `M`. This is the operation the logarithm version of the law would suggest for any reading. -/
def naiveDivideBack (x : ℚ_[3]) (M : ℕ) : ℝ := ‖x ^ M‖ / (M : ℝ)

/-- `‖2‖ = 1` in `ℚ_[3]` — the ingredient that makes `4 = 2 ^ 2` a unit rather than a multiple of
`3`. Quoted from `PadicLogVolume.norm_two_eq_one` at `p = 3`. -/
theorem norm_two_Q3 : ‖(2 : ℚ_[3])‖ = 1 :=
  PadicLogVolume.norm_two_eq_one (p := 3) (k := ℚ_[3]) (by decide) CoreLog.norm_three_lt_one
    (by decide)

/-- `‖4‖ = 1`: `4 = 2 ^ 2` and `‖2‖ = 1`. -/
theorem norm_four_Q3 : ‖(4 : ℚ_[3])‖ = 1 := by
  have h : (4 : ℚ_[3]) = 2 ^ 2 := by norm_num
  rw [h, norm_pow, norm_two_Q3, one_pow]

/-- `‖4 ^ 2‖ = 1`: `4 ^ 2 = 2 ^ 4` and `‖2‖ = 1`. The `M`-th power of a unit is a unit, which is
precisely why the naive reading has nothing to divide. -/
theorem norm_four_sq_Q3 : ‖((4 : ℚ_[3]) ^ 2)‖ = 1 := by
  have h : ((4 : ℚ_[3]) ^ 2) = 2 ^ 4 := by norm_num
  rw [h, norm_pow, norm_two_Q3, one_pow]

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`. This is what lets the *logarithm*
reading be applied at `x = 4`, so that the two readings are compared at the same input. -/
theorem norm_four_sub_one_Q3 : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- **The naive magnitude reading does not divide back.** A concrete failure at `x = 4`, `M = 2`:
`‖4 ^ 2‖ / 2 = 1 / 2`, but `‖4‖ = 1`. The two numbers are separated by `1 / 2 ≠ 1`, so no appeal to
any limiting or totalised quantity is involved: `4` is a unit, its square is a unit, and dividing a
unit's magnitude by `2` leaves `1 / 2`.

This is the anti-degeneracy statement of the file. The same `x` and the same `M` satisfy the
logarithm law (`divide_back_four_two`), so the difference between the two readings is not an artefact
of the input: it is the readings themselves. -/
theorem naive_magnitude_divide_back_fails :
    ‖(4 : ℚ_[3]) ^ 2‖ / (2 : ℝ) ≠ ‖(4 : ℚ_[3])‖ := by
  rw [norm_four_sq_Q3, norm_four_Q3]
  norm_num

/-- The same failure, stated with the named naive reading: `naiveDivideBack 4 2 ≠ naiveMagnitude 4`.
This is `naive_magnitude_divide_back_fails` after unfolding the two definitions and matching the cast
`((2 : ℕ) : ℝ)` of the definition with the literal `(2 : ℝ)` of the statement. -/
theorem naiveDivideBack_four_two : naiveDivideBack 4 2 ≠ naiveMagnitude 4 := by
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  simpa only [naiveDivideBack, naiveMagnitude, hcast] using naive_magnitude_divide_back_fails

/-- **Non-vacuity of the toy law at the same point.** At `x = 4` and `M = 2` — the very input at
which the naive reading fails — the logarithm version holds: `localLog 4 = localLog (4 ^ 2) / 2`.
Both sides are sums of a convergent series by `norm_four_sub_one_Q3` and `norm_pow_sub_one_lt_Q3`. -/
theorem divide_back_four_two :
    CoreTransport.localLog (4 : ℚ_[3]) =
      CoreTransport.localLog ((4 : ℚ_[3]) ^ 2) / (2 : ℚ_[3]) :=
  divide_back 4 norm_four_sub_one_Q3 2 (by norm_num)

end

end DivideBackLaw

#print axioms DivideBackLaw.algorithmRun
#print axioms DivideBackLaw.algorithmRun_eq_partialSums
#print axioms DivideBackLaw.localLog_eq_padicLog
#print axioms DivideBackLaw.hasSum_logTerm_localLog
#print axioms DivideBackLaw.norm_pow_sub_one_lt_Q3
#print axioms DivideBackLaw.localLog_pow_eq_smul
#print axioms DivideBackLaw.divide_back
#print axioms DivideBackLaw.naiveMagnitude
#print axioms DivideBackLaw.naiveDivideBack
#print axioms DivideBackLaw.norm_two_Q3
#print axioms DivideBackLaw.norm_four_Q3
#print axioms DivideBackLaw.norm_four_sq_Q3
#print axioms DivideBackLaw.norm_four_sub_one_Q3
#print axioms DivideBackLaw.naive_magnitude_divide_back_fails
#print axioms DivideBackLaw.naiveDivideBack_four_two
#print axioms DivideBackLaw.divide_back_four_two
