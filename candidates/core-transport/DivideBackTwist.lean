/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W8 toy province: divide-back **with the twist term written out**

**This file is a toy province for item (M-i) of the H3 prerequisites
(`research/core-backward-2026-10-23/h3-prerequisites.md`, §M-i), and nothing more.** It formalises
one shape and only that shape: *when the object whose `M`-th tensor power is read back is itself a
twist of a second object, the divide-back of the `M`-th power is the original reading **plus the
twist's own reading** — so "divide back by `M`" is harmless exactly when that extra term vanishes.*

## What the source says, and what it does not say

(Ob4), txt 8135–8144, and (Ob4-3), txt 8185–8189, only *assert* that the tensor-power-twist
indeterminacy "will not have any substantive effect on our computations"; (Ob4-3) states the claim
for **estimates** of log-volumes, not for exact equalities. No divide-back map is exhibited there,
no bound on the indeterminacy is given, and no invariance statement is proved. The obligation (M-i)
recorded in `h3-prerequisites.md` is precisely to replace the assertion by a named operation and an
explicit error term.

## What this file does

On `ℚ_[3]`, with the reading `CoreTransport.localLog` taken on the principal units
`‖z - 1‖ < 1`:

* `twistReading` — the reading of the `M`-th power of the *twisted* object `u * x` is
  `M * localLog u + M * localLog x`: the twist contributes its own full `M`-fold reading;
* `divideBack_twist` — dividing that by the scalar `M` gives `localLog u + localLog x`. The term
  `localLog u` is the twist's own reading; it is **not** removed by the divide-back, and it is
  named here as `twistResidue u`. The source's "no substantive effect" is therefore, in this toy,
  the assertion that this term vanishes or is absorbed — not something the divide-back does by
  itself;
* `twist_insensitive_iff` — the sharp form: the divide-back reading is insensitive to the twist for
  **every** admissible `x` if and only if `localLog u = 0`. Forward by taking `x = 1`; backward by
  rewriting the residue to zero. This is the statement that the source's assertion is exactly a
  vanishing statement;
* anti-degeneracy, twice over: `divideBack_twist_four_one` writes the identity out at `u = 4`,
  `x = 1`, `M = 2` (`localLog (4 ^ 2) / 2 = localLog 4 + localLog 1`), and `localLog_four_ne_zero`
  **proves**, rather than assumes, that the concrete twist reading `localLog 4` is non-zero — in
  fact `‖localLog 4‖ = 1/3` (`norm_localLog_four`), by the ultrametric domination of the leading
  term `4 - 1 = 3` over the tail. No root-of-unity hypothesis and no appeal to the kernel of the
  logarithm are needed for this witness.

## What this file does not say

It does **not** value the source's `M` (M-ii). It does **not** construct the divide-back map on the
tensor-power Frobenioids of (Ob4-1)/(Ob4-2)/(Ob4-3), and it proves nothing about the tensor-power
twist *as an object of the theory*: `ℚ_[3]` is a complete discretely valued field, not the
localisation of an arithmetic line bundle, and `x ↦ x ^ M` is not `det^{⊗M}`. It says **nothing**
about the two normalizations of (M-iii), nothing about log-volumes, log-shells, prime-strips,
Θ-links, `Ism`, Hodge theaters, Corollary 3.12, or any object of the audited `external/iut`
interfaces. In particular `localLog_four_ne_zero` does not exhibit a non-root-of-unity in the
source's fiber: it is a numerical witness inside `ℚ_[3]`, and no witness in the source's setting is
claimed. The `↔` of `twist_insensitive_iff` is a statement about this toy's reading, not a reading
of the source's "estimates". Nothing here is evidence for or against any IUT claim.

## Why declarations are restated instead of imported

`candidates/core-transport/lakefile.lean` declares the single library `CoreTransport`, whose modules
are the ones under `CoreTransport/`. `DivideBackLaw.lean` (W3) and `ExecutionProvenance.lean` sit at
the top level of the package, so they are not Lake targets, no `.olean` is produced for them, and
they cannot be imported. The declarations this file needs from them are therefore restated with the
same statements (`algorithmRun`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`,
`localLog_pow_eq_smul`); they carry no new mathematics. One deliberate difference is recorded:
`localLog_pow_eq_smul` is stated **without** the hypothesis `M ≠ 0`, because its upstream source
`PadicLogVolume.padicLog_pow` needs none; the `M ≠ 0` is needed only for *dividing* back, which is
why `divideBack_twist` does carry it.

The `p`-adic mathematics is quoted, not re-proved: `localLog_pow_eq_smul` is
`PadicLogVolume.padicLog_pow` (`candidates/core-log/PadicLogVolume/PadicLog.lean`) read through the
definition-level identification of the two literal series; convergence is
`CoreLog.principal_unit_log_hasSum`; multiplicativity is `PadicLogVolume.padicLog_mul`; the domain
condition for `u * x` is `PadicLogVolume.norm_mul_sub_one_lt`; the arithmetic input to the
non-vanishing proof is `PadicLogVolume.norm_natCast_eq_pow` and
`PadicLogVolume.factorization_lt_self`.
-/

namespace DivideBackTwist

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
`localLog_eq_padicLog`; it is the ingredient that makes `x = 1` usable in
`twist_insensitive_iff`. -/
theorem localLog_one : CoreTransport.localLog (1 : ℚ_[3]) = 0 := by
  rw [localLog_eq_padicLog 1]
  exact PadicLogVolume.padicLog_one

/-- **The reading of the `M`-th power is `M` times the reading.** Derived from
`PadicLogVolume.padicLog_pow` read through `localLog_eq_padicLog` at `x ^ M` and at `x`.

Unlike the W3 restatement in `DivideBackLaw.lean`, this carries **no** hypothesis `M ≠ 0`: upstream
`padicLog_pow` needs none, and the identity does hold at `M = 0` (both sides are `0`, since
`x ^ 0 = 1` and `localLog 1 = 0`). The hypothesis is carried by `divideBack_twist`, where it is
genuinely needed, for the division. -/
theorem localLog_pow_eq_smul (x : ℚ_[3]) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    CoreTransport.localLog (x ^ M) = (M : ℚ_[3]) * CoreTransport.localLog x := by
  rw [localLog_eq_padicLog (x ^ M), localLog_eq_padicLog x,
    PadicLogVolume.padicLog_pow (p := 3) (k := ℚ_[3]) (by decide) CoreLog.norm_three_lt_one hx M]

/-! ## 2. The twist term, made explicit -/

/-- **The twist's contribution before dividing back**: the reading of the twist `u`, carried to the
`M`-th power, i.e. `M` times `localLog u`. This is the term that the source asserts away; here it is
an object of the file, not a hypothesis. -/
def twistTerm (u : ℚ_[3]) (M : ℕ) : ℚ_[3] :=
  (M : ℚ_[3]) * CoreTransport.localLog u

/-- **What survives the divide-back**: the twist's own reading `localLog u`. Dividing by the scalar
`M` removes the factor `M` from the twist term but does not remove the term. -/
def twistResidue (u : ℚ_[3]) : ℚ_[3] :=
  CoreTransport.localLog u

/-- **The reading of a twisted `M`-th power.** For `‖u - 1‖ < 1` and `‖x - 1‖ < 1`, the reading of
`(u * x) ^ M` is `M * localLog u + M * localLog x`: the twist enters with a full `M`-fold reading of
its own, additively. The domain condition at the product `u * x` — a hypothesis of the multiplicative
law and of the power law alike — is supplied by `PadicLogVolume.norm_mul_sub_one_lt`. -/
theorem twistReading (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    CoreTransport.localLog ((u * x) ^ M) =
      (M : ℚ_[3]) * CoreTransport.localLog u + (M : ℚ_[3]) * CoreTransport.localLog x := by
  have hux : ‖u * x - 1‖ < 1 := PadicLogVolume.norm_mul_sub_one_lt hu hx
  have hmul : CoreTransport.localLog (u * x) =
      CoreTransport.localLog u + CoreTransport.localLog x := by
    rw [localLog_eq_padicLog (u * x), localLog_eq_padicLog u, localLog_eq_padicLog x]
    exact PadicLogVolume.padicLog_mul (p := 3) (k := ℚ_[3]) (by decide)
      CoreLog.norm_three_lt_one hu hx
  simp only [localLog_pow_eq_smul (u * x) hux M, hmul, mul_add]

/-- The same statement with the twist term named: the reading of the twisted `M`-th power is
`twistTerm u M` plus `M` times the reading of `x`. -/
theorem twistReading_twistTerm (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    CoreTransport.localLog ((u * x) ^ M) =
      twistTerm u M + (M : ℚ_[3]) * CoreTransport.localLog x :=
  twistReading u x hu hx M

/-- **Divide-back of a twisted `M`-th power — the twist term is still there.** Dividing the reading
of `(u * x) ^ M` by the scalar `M` gives `localLog u + localLog x`, not `localLog x`. The extra
summand is the twist's own reading `twistResidue u`; it is *not* removed by the divide-back, and it
is exactly the quantity whose vanishing the source asserts. The hypothesis `M ≠ 0` is what the
division needs, via `Nat.cast_ne_zero`. -/
theorem divideBack_twist (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ)
    (hM : M ≠ 0) :
    CoreTransport.localLog ((u * x) ^ M) / (M : ℚ_[3]) =
      CoreTransport.localLog u + CoreTransport.localLog x := by
  have hM' : (M : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.2 hM
  simp only [twistReading u x hu hx M, add_div, mul_div_cancel_left₀ (CoreTransport.localLog u) hM',
    mul_div_cancel_left₀ (CoreTransport.localLog x) hM']

/-- The same statement with the surviving term named: the divide-back of the twisted `M`-th power is
`twistResidue u + localLog x`. -/
theorem divideBack_twist_residue (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ)
    (hM : M ≠ 0) :
    CoreTransport.localLog ((u * x) ^ M) / (M : ℚ_[3]) =
      twistResidue u + CoreTransport.localLog x :=
  divideBack_twist u x hu hx M hM

/-- **Twist-insensitivity holds if and only if the twist's reading vanishes.** The divide-back
reading is insensitive to the twist `u` for *every* admissible `x` exactly when `localLog u = 0`.

* Forward: apply the insensitivity at `x = 1`, where `divideBack_twist` reads
  `localLog ((u * 1) ^ M) / M = localLog u + localLog 1` and `localLog 1 = 0`, while the assumed
  insensitivity reads the same left-hand side as `localLog 1 = 0`; hence `localLog u = 0`.
* Backward: rewrite the residue in `divideBack_twist` to zero.

This is the sharp reading of (Ob4-3)'s "no substantive effect": in this toy the assertion is
*equivalent* to the vanishing of a single term, not a consequence of the divide-back. -/
theorem twist_insensitive_iff (u : ℚ_[3]) (hu : ‖u - 1‖ < 1) (M : ℕ) (hM : M ≠ 0) :
    (∀ x : ℚ_[3], ‖x - 1‖ < 1 →
        CoreTransport.localLog ((u * x) ^ M) / (M : ℚ_[3]) = CoreTransport.localLog x) ↔
      CoreTransport.localLog u = 0 := by
  constructor
  · intro h
    have hx1 : ‖(1 : ℚ_[3]) - 1‖ < 1 := by norm_num
    have hinst : CoreTransport.localLog ((u * 1) ^ M) / (M : ℚ_[3]) = 0 := by
      rw [h 1 hx1, localLog_one]
    have htw : CoreTransport.localLog ((u * 1) ^ M) / (M : ℚ_[3]) =
        CoreTransport.localLog u := by
      rw [divideBack_twist u 1 hu hx1 M hM, localLog_one, add_zero]
    exact htw.symm.trans hinst
  · intro h x hx
    rw [divideBack_twist u x hu hx M hM, h, zero_add]

/-! ## 3. Anti-degeneracy: the identity written out, and a non-zero twist reading -/

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`, so the reading may be taken at
`x = 4` and at the twist `u = 4` alike. -/
theorem norm_four_sub_one_Q3 : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- **The identity at `u = 4`, `x = 1`, `M = 2`**, exactly as `divideBack_twist` delivers it:
`localLog ((4 * 1) ^ 2) / 2 = localLog 4 + localLog 1`. The right-hand side visibly carries the
twist's reading `localLog 4` as an addend. -/
theorem divideBack_twist_four_one :
    CoreTransport.localLog (((4 : ℚ_[3]) * 1) ^ 2) / (2 : ℚ_[3]) =
      CoreTransport.localLog (4 : ℚ_[3]) + CoreTransport.localLog (1 : ℚ_[3]) :=
  divideBack_twist 4 1 norm_four_sub_one_Q3 (by norm_num) 2 (by norm_num)

/-- The same identity with `4 * 1` written as `4 ^ 2`: `localLog (4 ^ 2) / 2 =
localLog 4 + localLog 1`. -/
theorem divideBack_twist_four_one_sq :
    CoreTransport.localLog ((4 : ℚ_[3]) ^ 2) / (2 : ℚ_[3]) =
      CoreTransport.localLog (4 : ℚ_[3]) + CoreTransport.localLog (1 : ℚ_[3]) := by
  simpa using divideBack_twist_four_one

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
norm `1/3`, and the whole tail has norm at most `1/9 < 1/3`; by the ultrametric maximum principle
the reading has exactly the size of its leading term. -/
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

/-- **The concrete twist reading is non-zero.** `localLog 4 ≠ 0`, because its norm is `1/3`. This is
the witness the toy needs: at `u = 4` the twist term in `divideBack_twist` is a genuinely non-zero
addend, so "divide back by `M`" alone does not make the reading insensitive to the twist. -/
theorem localLog_four_ne_zero : CoreTransport.localLog (4 : ℚ_[3]) ≠ 0 := by
  intro h
  have hnorm := norm_localLog_four
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-- The same non-vanishing for the named residue: `twistResidue 4 ≠ 0`. -/
theorem twistResidue_four_ne_zero : twistResidue (4 : ℚ_[3]) ≠ 0 :=
  localLog_four_ne_zero

end

end DivideBackTwist

#print axioms DivideBackTwist.algorithmRun
#print axioms DivideBackTwist.algorithmRun_eq_partialSums
#print axioms DivideBackTwist.localLog_eq_padicLog
#print axioms DivideBackTwist.hasSum_logTerm_localLog
#print axioms DivideBackTwist.localLog_one
#print axioms DivideBackTwist.localLog_pow_eq_smul
#print axioms DivideBackTwist.twistTerm
#print axioms DivideBackTwist.twistResidue
#print axioms DivideBackTwist.twistReading
#print axioms DivideBackTwist.twistReading_twistTerm
#print axioms DivideBackTwist.divideBack_twist
#print axioms DivideBackTwist.divideBack_twist_residue
#print axioms DivideBackTwist.twist_insensitive_iff
#print axioms DivideBackTwist.norm_four_sub_one_Q3
#print axioms DivideBackTwist.divideBack_twist_four_one
#print axioms DivideBackTwist.divideBack_twist_four_one_sq
#print axioms DivideBackTwist.norm_three_sq_Q3
#print axioms DivideBackTwist.norm_logTerm_four_le
#print axioms DivideBackTwist.norm_localLog_four
#print axioms DivideBackTwist.localLog_four_ne_zero
#print axioms DivideBackTwist.twistResidue_four_ne_zero
