# W9 — M-ii toy: **what determines the exponent `M`, and what leaves it undetermined**

Date: 2026-10-23. Scope: **(M-ii) of `research/core-backward-2026-10-23/h3-prerequisites.md`, toy
shape only.** Not a fact-tree node, not a registry entry, not evidence for or against any IUT claim.

## Deliverable

One new file, and nothing else in the candidate tree:

| item | value |
|---|---|
| file | `candidates/core-transport/ExponentUniqueness.lean` (**did not exist** before this round — checked at start; created, not overwritten) |
| namespace | `ExponentUniqueness` |
| lines / bytes | 362 / 21471 (LF only, no CR, final newline, no BOM) |
| sha256 | `7857AD77B04BA3926A90DA1CDA3B51B32BC1C69FDA4C80FD13C0D93DCF3CC52D` |
| declarations | 18 (`1` `def`, `17` theorems), **each** followed by `#print axioms` at the file end |
| build | exit code **0**, stdout 1843 B (the 18 axiom lines and nothing else), **stderr 0 B** |

No existing file was modified: `tools/`, fact-tree, registry, and the other candidates are untouched.

## Commands

Built from `candidates/core-transport`:

```
lake env lean -DwarningAsError=true ExponentUniqueness.lean
```

Raw logs in this directory, captured with `cmd /c "... 1> ... 2> ..."` so byte counts are real and no
UTF-16/BOM artefact enters them:

* `compile.stdout.log` — 1843 B, the 18 `#print axioms` lines and nothing else;
* `compile.stderr.log` — **0 B**;
* `compile.exit.txt` — exit code `0`.

## Repair rounds

One round, linter only, no mathematics:

* Round 1. `ExponentUniqueness.lean:306:51: error: Variable name 'hMN' is not explicitly referenced.`
  — `-DwarningAsError=true` turns `linter.unusedVariables` into a hard error. `hMN : M ≠ N` is an
  explicit hypothesis that occurs in the *type* but is never used in the *proof* (the zero reading
  makes the two sides equal for **all** `M`, `N`), so it cannot be referenced honestly.
* Fix: `set_option linter.unusedVariables false in` placed **before** the docstring it applies to
  (line 294), keeping the required statement with the binder name `hMN` verbatim. No statement and no
  proof changed. Round 2 compile: exit 0, stderr 0 B.

Note on lemma availability: the installed Mathlib's ultrametric lemmas used in the non-vanishing
proof (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`,
`IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`) exist as `to_additive`-generated names; they
were checked by name resolution at compile time, not assumed from a doc.

## Axioms

All 18 declarations — the `def` included — print exactly:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Verbatim sample (identical for every entry; see `compile.stdout.log`):

```
'ExponentUniqueness.log4_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExponentUniqueness.power_reading_injective_on_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExponentUniqueness.not_determined_by_torsion_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Axiom set ⊆ `{propext, Classical.choice, Quot.sound}`.

Forbidden-substring scan on the file (docstrings included): `sorry` **0**, `admit` **0**, `opaque`
**0**, `native_decide` **0**, `\baxiom\b` **0**. The only occurrences of the letters `axiom` are the
18 required `#print axioms` lines (`axioms` does not match `\baxiom\b`).

## The three required statements (verbatim)

`ExponentUniqueness.lean:270`

```lean
theorem power_reading_injective_on_probe (M N : ℕ) :
    CoreTransport.localLog ((4 : ℚ_[3]) ^ M) = CoreTransport.localLog ((4 : ℚ_[3]) ^ N) ↔
      M = N
```

`ExponentUniqueness.lean:288`

```lean
theorem exponent_determined (M N : ℕ)
    (h : ∀ x : ℚ_[3], CoreTransport.localLog (x ^ M) = CoreTransport.localLog (x ^ N)) : M = N
```

`ExponentUniqueness.lean:307`

```lean
theorem not_determined_by_torsion_probe (M N : ℕ) (hMN : M ≠ N) :
    CoreTransport.localLog ((1 : ℚ_[3]) ^ M) = CoreTransport.localLog ((1 : ℚ_[3]) ^ N)
```

The engine is `log4_ne_zero : CoreTransport.localLog (4 : ℚ_[3]) ≠ 0` (line 243), a **theorem in this
file**, proved from `norm_localLog_four : ‖localLog 4‖ = 1/3` (line 205), which is itself proved by the
leading-term/tail split of the logarithm series at `4` (leading term `4 - 1 = 3`, norm `1/3`; tail
bounded termwise by `‖3‖^2 = 1/9`; ultrametric maximum principle). Nothing is assumed.

## How `log4` was cancelled

```lean
rw [reading_pow_four M, reading_pow_four N] at h
have hcast : (M : ℚ_[3]) = (N : ℚ_[3]) := mul_right_cancel₀ log4_ne_zero h
exact Nat.cast_injective (R := ℚ_[3]) hcast
```

`reading_pow_four` is `localLog_pow_eq_smul 4 norm_four_sub_one_Q3` (`localLog (4^M) = M * localLog 4`),
so the hypothesis becomes `M * log4 = N * log4`; `mul_right_cancel₀` uses `log4_ne_zero` (a non-zero
element of the field `ℚ_[3]` is cancellable on the right) to give the equality of the scalar casts, and
`Nat.cast_injective` converts it to `M = N`. Backward direction: `rw [h]`.

At the torsion probe the same rewrite yields `M * 0 = N * 0`, and `log4_ne_zero` has no analogue at
`1`: `localLog_one` is exactly the vanishing that blocks the cancellation.

## Anti-degeneracy: what is proved, not assumed

* `norm_logTerm_four_le`, `norm_three_sq_Q3`, `norm_four_sub_one_Q3`, `norm_localLog_four`,
  `log4_ne_zero` — the non-vanishing of the probe's reading, re-derived here in full.
* `reading_pow_four` — the power law written at the probe.
* `log_eq_zero_of_pow_eq_one` — the root-of-unity shape (W1's shape), via
  `PadicLogVolume.padicLog_eq_zero_of_pow_eq_one`.
* `not_determined_by_zero_reading` — every probe with *zero* reading fails to determine the exponent:
  no hypothesis relates `M` and `N`, so the failure is a property of the reading's value, not of the
  element `1`.
* `torsion_probe_determines_nothing` — a root-of-unity probe determines nothing (contains the unit
  case `n = 1`).

## Non-claims (stated in the module docstring as well)

1. Does **not** identify the source's three `M`s (hull `det^{⊗M}`, q-pilot `M`-th tensor power,
   (Ob4-1) degree-`M` Frobenius). It shows what shape an identification would need, not that the
   three agree.
2. Does **not** value `M`. `ℚ_[3]` is a complete discretely valued field; `x ↦ x ^ M` is not
   `det^{⊗M}`; `CoreTransport.localLog` is the `p`-adic logarithm, not a log-volume; no probe in the
   source's setting is exhibited.
3. Does **not** say the source's "uniquely determined" is false, nor that `cf. N_E` is unfounded —
   only that a bare "cf." supplies no probe, hence no determination *in the toy's sense*.
4. Says nothing about the two normalizations of (M-iii), log-volumes, log-shells, prime-strips,
   Θ-links, `Ism`, Hodge theaters, Corollary 3.12, or any audited `external/iut` interface.

## Restatement note (why nothing was imported)

`candidates/core-transport/lakefile.lean` declares the single library `CoreTransport`, whose modules
are those under `CoreTransport/`. `DivideBackTwist.lean` (W8), `DivideBackLaw.lean` (W3) and
`ExecutionProvenance.lean` are top-level modules of the package: not Lake targets, no `.olean`,
therefore **not importable**. The declarations needed are restated with the same statements —
`algorithmRun`, `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`,
`localLog_one`, `localLog_pow_eq_smul` — and carry no new mathematics. As in W8,
`localLog_pow_eq_smul` is stated **without** `M ≠ 0`, since `PadicLogVolume.padicLog_pow` needs none.
