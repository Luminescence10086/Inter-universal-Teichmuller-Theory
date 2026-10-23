# W10 — the H3 synthesis of (M-i) and (M-ii): one homomorphic reading, one non-torsion probe

Date: 2026-10-23. Scope: **the synthesis of the two toy provinces W8 (`DivideBackTwist.lean`, item
M-i) and W9 (`ExponentUniqueness.lean`, item M-ii), and nothing else.** Not a fact-tree node, not a
registry entry, not evidence for or against any IUT claim.

## Deliverable

| item | value |
|---|---|
| file | `candidates/core-transport/H3Synthesis.lean` (**did not exist** before this round — checked at start; created, not overwritten) |
| namespace | `H3Synthesis` |
| lines / bytes | 344 / 20393 (LF only, no CR, final newline, no BOM) |
| sha256 | `6C642F6C353876BCB3012A2BECA42205CFA4114DC7794693DE8318E48EE1B381` |
| declarations | 21 (`4` `def`s, `17` theorems), **each** followed by `#print axioms` at the file end |
| build | exit code **0**, stdout 1860 B (the 21 axiom lines and nothing else), **stderr 0 B** |

No existing file was modified: `tools/`, fact-tree, registry, the other candidates and the two toys
are untouched (`H3Synthesis.lean` is the only addition; `git status` shows it as untracked).

## Commands

Built from `candidates/core-transport`:

```
lake env lean -DwarningAsError=true H3Synthesis.lean
```

Raw logs in this directory, captured with `cmd /c "... 1> ... 2> ..."` so byte counts are real and no
UTF-16/BOM artefact enters them:

* `compile.stdout.log` — 1860 B, the 21 `#print axioms` lines and nothing else;
* `compile.stderr.log` — **0 B**;
* `compile.exit.txt` — exit code `0`.

## The encoding, and why it is not literally `G →+ ℚ_[3]`

`AddMonoidHom` requires an `AddMonoid` on its *domain*; a `CommGroup` supplies none, so `G →+ ℚ_[3]`
does not typecheck for `[CommGroup G]`. The reading is therefore `R : G →* Multiplicative ℚ_[3]`
(whose multiplication **is** the addition of `ℚ_[3]`), and `reading R x = (R x).toAdd` is its additive
shadow. Nothing is lost: `reading_eq_toAdditiveLeft` proves `reading R x = MonoidHom.toAdditiveLeft R
(Additive.ofMul x)`, i.e. `R` *is* an additive monoid homomorphism `Additive G →+ ℚ_[3]` by Mathlib's
`MonoidHom.toAdditiveLeft`, and `reading_mul` gives the additivity `reading R (x * y) = reading R x +
reading R y` used everywhere. Commutativity is never used (`CommGroup` is kept only because the task's
and the toys' groups are commutative). The free reading of §4 is the same encoding in the other
direction: `freeReading = (Int.castAddHom ℚ_[3]).toMultiplicative`.

## Axioms

All 21 declarations — the `def`s included — print a subset of `{propext, Classical.choice,
Quot.sound}` (19 print exactly that set; `probeOne` and `twistFour` print only `[Quot.sound]`).
Verbatim sample (see `compile.stdout.log` for all 21):

```
'H3Synthesis.reading_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'H3Synthesis.exponent_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'H3Synthesis.comparison_well_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
'H3Synthesis.comparison_fails_at_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Axiom set ⊆ `{propext, Classical.choice, Quot.sound}`.

Forbidden-substring scan on the file (docstrings included): `sorry` **0**, `admit` **0**, `opaque` **0**,
`native_decide` **0**, `\baxiom\b` **0**. The only occurrences of the letters `axiom` are the 21
required `#print axioms` lines.

## The four required statements (verbatim)

`H3Synthesis.lean:146`

```lean
theorem reading_pow (R : G →* Multiplicative ℚ_[3]) (x : G) (M : ℕ) :
    reading R (x ^ M) = M • reading R x
```

`H3Synthesis.lean:164`

```lean
theorem exponent_unique (R : G →* Multiplicative ℚ_[3]) (x : G) (hx : reading R x ≠ 0) {M N : ℕ} :
    reading R (x ^ M) = reading R (x ^ N) ↔ M = N
```

`H3Synthesis.lean:185`

```lean
theorem twist_free_iff (R : G →* Multiplicative ℚ_[3]) (u : G) :
    reading R u = 0 ↔ ∀ x : G, reading R (u * x) = reading R x
```

`H3Synthesis.lean:222`

```lean
theorem comparison_well_defined (R : G →* Multiplicative ℚ_[3]) (u x : G) (hu : reading R u = 0)
    (hx : reading R x ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    reading R (u * x ^ M) / (M : ℚ_[3]) = reading R x
```

`divideBack_abstract` (line 201) is the intermediate step both toys' divide-back shares:
`reading R (u * x ^ M) / (M : ℚ_[3]) = reading R u / (M : ℚ_[3]) + reading R x`.

## The two degeneracy witnesses (concrete, with numbers)

Both live in the free commutative group `Multiplicative ℤ` (multiplication = addition of `ℤ`), so every
number is literal and no `p`-adic analysis is redone.

1. **Zero reading kills (M-ii).** `trivialReading` sends everything to `0`; the probe is
   `probeOne = ofAdd 1`, which is **not** the identity (`probeOne_ne_one`) yet reads `0`
   (`zeroReading_probeOne`). Then `exponent_unique_fails_at_zero_reading` states, in one conjunction,
   `probeOne ≠ 1`, `reading = 0`, equal readings at the exponents `0` and `1`, and `(0 : ℕ) ≠ 1`. The
   abstract form is `zero_reading_powers_agree`: a zero-reading probe determines nothing at all.
2. **A non-zero twist breaks the comparison (M-i).** `freeReading = (Int.castAddHom
   ℚ_[3]).toMultiplicative` gives `reading (ofAdd n) = n`; `twistFour = ofAdd 4` therefore reads `4 ≠ 0`
   (`reading_twistFour_ne_zero`), so the hypothesis `hu` of `comparison_well_defined` is false at these
   numbers. `comparison_fails_at_four` states the failure as an inequality of the two readings, at W8's
   numbers (`u = 4`, `x = 1`, `M = 2`):

   ```lean
   theorem comparison_fails_at_four :
       reading freeReading (twistFour * (1 : Multiplicative ℤ) ^ 2) / ((2 : ℕ) : ℚ_[3]) ≠
         reading freeReading (1 : Multiplicative ℤ)
   ```

   the left side reads `4 / 2 = 2`, the right side reads `0`. One deliberate difference from W8: the
   twist reading here is the integer `4`, not W8's `localLog 4 ∈ ℚ_[3]` (whose non-vanishing W8 proves
   as `‖localLog 4‖ = 1/3`); that estimate is not redone, and it is not what the witness tests. The
   load-bearing hypothesis `reading R u ≠ 0` holds in both.

## Repair rounds

Two compile rounds, both mechanical, no statement and no proof strategy abandoned:

* Round 1 (three diagnostics, one line each):
  1. `H3Synthesis.lean:150:48: error(lean.unknownIdentifier): Unknown identifier 'nsmul_succ'` — in
     this Mathlib the `to_additive` name of `pow_succ` is `succ_nsmul`
     (`(n + 1) • a = n • a + a`), checked by name resolution, not assumed. Replaced `nsmul_succ` by
     `succ_nsmul`. Nothing else changed in the induction.
  2. `H3Synthesis.lean:218:5: error: Variable name 'hx' is not explicitly referenced.` — under
     `-DwarningAsError=true` the `linter.unusedVariables` linter is a hard error, and `hx : reading R x
     ≠ 0` occurs in the *statement* (where it carries the non-torsion content) but not in the proof.
     Fix: `set_option linter.unusedVariables false in` placed **before** the docstring it applies to,
     keeping the required statement verbatim; the reason is also recorded in the declaration's
     docstring.
  3. `H3Synthesis.lean:311:6: error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern
     reading freeReading (twistFour * 1 ^ 2) / ↑2` — the goal's denominator was written `(2 : ℚ_[3])`
     (`OfNat`), while `divideBack_abstract`'s conclusion carries `(M : ℚ_[3])` with `M := 2`, i.e.
     `Nat.cast 2`; the two are propositionally but not syntactically equal. Fix: state the goal's
     denominator as `((2 : ℕ) : ℚ_[3])` (so the rewrite matches syntactically) and derive `4 / 2 = 2`
     by `mul_div_cancel_left₀` from `4 = 2 * 2`, with `((2 : ℕ) : ℚ_[3]) ≠ 0` by `Nat.cast_ne_zero` —
     no division evaluation by `norm_num` is relied on.
* Round 2 (after a small docstring edit and the bundling of the first witness into one conjunction):
  exit code 0, stdout 1860 B (21 axiom lines), stderr 0 B. This is the state recorded above.

## Non-claims (stated in the module docstring as well)

1. **No IUT object is claimed to carry such an `R`.** `ℚ_[3]` is the `p`-adic field, not a log-volume;
   `reading R` is neither `localLog` nor a log-volume of any arithmetic line bundle; `x ↦ x ^ M` is
   not `det^{⊗M}`.
2. **No `p`-adic analysis is redone.** The toys' `localLog 4 ≠ 0` is W8's `norm_localLog_four`; it is
   neither restated nor used. The file's witnesses need only `CharZero ℚ_[3]`.
3. **The abstraction is honest in one precise sense only**: it isolates the two facts the two toys
   actually use (additivity of the reading, non-vanishing of the probe's reading) and derives exactly
   what those two facts imply. It says what W8 and W9 *share* — not that anything in IUT supplies such
   a reading, and not that the source's assertions about the tensor-power twist and about the
   "uniquely determined" `M` are true or false. Both remain open as recorded in
   `research/core-backward-2026-10-23/m-i-design.md` and `m-ii-design.md`.
4. Says nothing about the two normalizations of (M-iii), log-volumes, log-shells, prime-strips,
   Θ-links, `Ism`, Hodge theaters, Corollary 3.12, or any audited `external/iut` interface.
