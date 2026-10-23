# W2 — local-global collection provenance toy (`CollectionProvenance.lean`)

Task: item 2 of the current goal — lift the K4 execution-provenance type
(`candidates/core-transport/ExecutionProvenance.lean`) from a **single element** to a **local-global
collection**, and prove that provenance determines the reading of the *whole collection*, not only of
one piece. The collection models cQ3's `⊼lc-gl_1..3` shape — local objects, one global object,
localisation between them (`research/core-backward-2026-10-23/h1-decision.md`, §结论二;
`h1-coricity.md` for the "up to isomorphism" side).

## Scope

One new Lean file, **new** (verified absent before writing):

* `candidates/core-transport/CollectionProvenance.lean` — namespace `CollectionProvenance`,
  526 lines, 31056 bytes.
* No existing file was modified. Nothing in `tools/`, the fact-tree, the registry, or any other
  candidate or book was touched. No `lake update`, no Mathlib rebuild.

`ExecutionProvenance.lean` is **not importable**: `lakefile.lean` declares only `lean_lib CoreTransport`,
so that module is not a Lake target, no `ExecutionProvenance.olean` is produced, and the file was
checked standalone (the same holds for `ReadingInvariance.lean`). `algorithmRun`,
`localLog_eq_padicLog` and `hasSum_logTerm_localLog` are therefore re-stated/re-derived inside the new
file, exactly as K4 and W1 each did, and the module docstring says so in those words. Those
re-derivations are identifications of two literal series by unfolding both definitions; they add no
mathematical content.

## What the file contains

| declaration | role |
|---|---|
| `algorithmRun x n` | the partial-sum algorithm of the logarithm on `ℚ_[3]`, documented as a re-statement of K4's |
| `algorithmRun_eq_partialSums` | that partial sum is literally the partial sum of `PadicLogVolume.logTerm`, definitionally |
| `localLog_eq_padicLog` | the two literal series are one series, by unfolding both definitions |
| `hasSum_logTerm_localLog` | the existing convergence theorem, **quoted** (`CoreLog.principal_unit_log_hasSum`) |
| `structure LocalGlobalCollection (n)` | **item 3** — `localInput`/`mem`, `localSteps`/`steps_eq`, `localValue`/`converges`, `globalValue`/`localization`, i.e. `⊼lc-gl`'s shape at the set level |
| `localSteps_eq_algorithm` | `steps_eq` read as one statement: the trace function *is* the algorithm at the input function |
| `localValue_determined` | **item 4** — componentwise: `c.localValue v = localLog (c.localInput v)`, from `converges v` + `steps_eq v` + the quoted theorem, by uniqueness of limits |
| `localValues_determined` | the **whole** local reading function is determined, not one component |
| `globalValue_determined_at` | the global reading is determined at any index |
| `globalValue_determined` | **item 5** — `c.globalValue = localLog (c.localInput 0)` for `Fin (n+1)` |
| `both_readings_unique` | same `localInput` ⇒ same local reading function **and** same global reading |
| `localValue_mem_logImage`, `SatisfiesLanding`, `landing_of_provenance` | landing is a **consequence**, proved of every collection; it is not a field |
| `logImage_Q3_eq_closedBall` | the log image is the whole closed ball of radius `1/3`, so landing is weak |
| `norm_four_sub_one`, `norm_neg_two_sub_one`, `norm_one_sub_one` | `4`, `-2`, `1` are principal units |
| `norm_two_Q3`, `norm_two_mul_three`, `norm_three_le_two_mul_three` | `‖2‖ = 1`, `‖2·3‖ = ‖3‖ = 1/3`, so `3` and `-3` lie in the ball of radius `‖2p‖` |
| `norm_logRem_three_le`, `norm_logRem_neg_three_le` | `‖logRem (±3)‖ ≤ 1/9`, from the existing estimate `PadicLogVolume.norm_logRem_le` |
| `localLog_one`, `localLog_four`, `localLog_neg_two` | `log 1 = 0`, `log 4 = 3 + logRem 3`, `log (-2) = -3 + logRem (-3)`, from `PadicLogVolume.padicLog_one_add` |
| `localLog_four_ne_zero`, `localLog_four_ne_localLog_negTwo` | the two concrete separations of readings |
| `witnessFour`, `witnessNegTwo`, `witnessOne` | three fully discharged `LocalGlobalCollection 1`; every field proved (`steps_eq` by `rfl`) |
| `landing_does_not_determine_global` | **item 6, the point of the file** |
| `landing_does_not_determine_global_nontrivial` | **item 6**, same separation with both inputs ≠ `1` |

### Item 5: the shape choice

`globalValue_determined` is stated for `LocalGlobalCollection (n + 1)` and uses the index `0`, so that
`0 : Fin (n+1)` needs no side condition (no `[NeZero n]` hypothesis). The general
`globalValue_determined_at` holds at *every* index and for every `n` and is strictly stronger; the
required `0`-statement is its specialisation. This is said in the docstring of the theorem itself.

### Item 6: which anti-degeneracy statement is proved, and what is impossible

**Proved (the preferred form, not the fallback).** `landing_does_not_determine_global` exhibits **two
collections with the same `n`** (`n = 1`), each of whose local readings lies in
`CoreTransport.logImage ℚ_[3]` — both satisfy the landing predicate, and `landing_of_provenance` proves
that predicate of *any* collection — whose **global readings differ** (`log 4 ≠ log 1`).
`landing_does_not_determine_global_nontrivial` repeats it with inputs `4` and `-2`, both principal units
different from `1`, so the failure is not an artefact of the trivial input.

**Not needed: the fallback.** The task allowed falling back to "one collection with `n = 1` against one
with `n = 2`" if the toy's `localization` field made the same-`n` statement impossible. It does **not**:
`localization` relates the global reading of *one* collection to *its own* local readings, and says
nothing about comparing two different collections. Since two collections with `n = 1` may have different
local readings, they may have different global readings — which is what is proved.

**Impossible in this toy (stated, not silently dropped).** "Same local readings, different global
reading" is impossible: `both_readings_unique` proves that two collections with the same `localInput`
have the same `localValue` function *and* the same `globalValue`. So any separation must be produced by
data the landing predicate does not see — the inputs. That is precisely the honest content:

> **"Each local piece is produced by the algorithm" is a statement about the trace (it pins the value by
> definitional equality with `algorithmRun` at a given input, hence forces a *particular* reading),
> whereas "the global reading is a landing condition" is a statement that the reading lies somewhere in
> a region — and a region of radius `1/3` contains readings of collections that disagree, so it
> determines no reading at all.**

**Toy stand-in, stated as such.** `localization` is the single equation `globalValue = localValue v`
for every `v` ("the global reading is the common local reading"). In the source it is a family of
localisation *morphisms* between genuinely different objects with a compatibility structure. It is the
crudest relation of the required shape, it captures only that the global reading is tied to the local
ones, and it is **not** IUT's localisation. The module docstring says this in those terms.

## Commands

From `candidates/core-transport` (toolchain `leanprover/lean4:v4.34.0-rc2`, `lake-manifest.json`
unchanged):

```
lake env lean -DwarningAsError=true CollectionProvenance.lean
```

Result: **exit code 0**, `-DwarningAsError=true`, **stderr 0 bytes**, stdout 6702 bytes
(= the 32 required `#print axioms` lines; two of them wrap, hence 34 physical lines).

```
sha256  CDDEA79C5DF62CD2E3AD999206526D449434798FD741E7E5371E6150FA601422
bytes   31056
lines   526
```

Machine: Windows, `pwsh`, `D:\` native workspace; `lake env lean --version` reports
`Lean (version 4.34.0-rc2, x86_64-w64-windows-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d)`.
No `.olean` is produced next to the source by `lake env lean`, so the package directory still contains
no compiled artifact for this module (consistent with the "not importable" statement above).

## Per-theorem axioms (verbatim, all 32 lines)

`propext, Classical.choice, Quot.sound` for every one of them; no line contains anything else. The last
two wrap across three physical lines in the log; they are reprinted here joined for readability, and
`W2_stdout.log` holds the byte-exact output.

```
'CollectionProvenance.algorithmRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.algorithmRun_eq_partialSums' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_eq_padicLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.hasSum_logTerm_localLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localSteps_eq_algorithm' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localValue_determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localValues_determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.globalValue_determined_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.globalValue_determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.both_readings_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localValue_mem_logImage' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.SatisfiesLanding' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.landing_of_provenance' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.logImage_Q3_eq_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_four_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_neg_two_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_one_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_two_Q3' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_two_mul_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_three_le_two_mul_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_logRem_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.norm_logRem_neg_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_four_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.localLog_four_ne_localLog_negTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.witnessFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.witnessNegTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.witnessOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.landing_does_not_determine_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollectionProvenance.landing_does_not_determine_global_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Forbidden-substring scan (whole file, case-insensitive, docstrings included)

```
sorry = 0    admit = 0    opaque = 0    native_decide = 0    axiom = 32
```

The 32 hits for `axiom` are exactly the 32 required `#print axioms` commands — nothing else in the file
contains the string. No declaration in the file is a placeholder; every proof term is complete.

## Repair history (honest)

Four elaborations of the file were run; the accepted one is the fourth.

1. **Build 1 — exit 1** (`W2_build_errors.md`, verbatim). Two genuine problems: the unused-variable
   linter rejected the structure's `∀ v, ℕ → ℚ_[3]` / `∀ v, ℚ_[3]` binders under `-DwarningAsError`, and
   two `calc` steps failed because `rw [CoreLog.norm_three]` rewrites `‖(3 : ℚ_[3])‖` but not the
   syntactically different `‖((3 : ℕ) : ℚ_[3])‖` occurring in `norm_logRem_le`'s conclusion.
2. **Repair 1 (substantive)** — the two lemmas now bridge with
   `simpa only [Nat.cast_ofNat, (norm_neg,) CoreLog.norm_three]` instead of `rw`; both proofs then close
   with no change to their statements. This was the only proof-level repair.
3. **Repairs 2–3 (mechanical, same file, no proof changed)** — the linter workaround was first written
   as `set_option … in` and then as a bare command *after* a docstring; Lean rejects a `set_option`
   command in either position immediately following a docstring, because a docstring must be followed by
   its declaration. Both attempts failed with the identical single error
   `unexpected token 'set_option'; expected 'lemma'`. Fixed by placing the option command **before** the
   structure's docstring and restoring the linter immediately after the structure.
4. **Build 4 — exit 0**, stderr 0 bytes (the accepted run, `W2_stdout.log` / `W2_stderr.log`).

Note on the task's two-round limit: only **one** repair round touched a failing proof obligation; rounds
2–3 were placement fixes for a `set_option` command and changed no statement or proof. No failing proof
was left in the file at any point.

## What this does NOT establish

* It does not formalise `⊼lc-gl`, `⊼fQ₁`, `⊼fQ₂`, the formal quotient `⊼fQ₂ modulo ⊼fQ₁`, the Θ-link, the
  η-algorithm, `Ism`, Corollary 3.12, prime-strips, Frobenioids, Hodge theaters, coricity, or any Galois
  action. `Fin n` is a set of indices, **not** a set of places; `localization` is one equation, **not** a
  family of localisation morphisms; the `ℚ_[3]` logarithm series is **not** the η-algorithm.
* It does not show that provenance-typed interfaces suffice for the real local-global collections, nor
  that the reading of the real object is a limit at all. It shows one shape is consistent and provable on
  one concrete complete field.
* It proves nothing new about the p-adic logarithm: convergence (`CoreLog.principal_unit_log_hasSum`), the
  rearrangement `padicLog_one_add`, the remainder estimate `norm_logRem_le` and the image computation
  `principal_unit_log_image` are all quoted from the existing libraries. The only arithmetic done here is
  `‖logRem (±3)‖ ≤ 1/9` and the resulting `log 4 ≠ 0`, `log 4 ≠ log (-2)`.
* It is not evidence for or against any IUT claim, and it does not touch the 11 audited interfaces of
  `handoffs/core-backward-2026-10-23/M3/` (it only records, in a docstring, that their analogue of
  landing is a structure field).

## Logs in this directory

* `W2_stdout.log` (6702 bytes) — accepted build, exit 0: the 32 `#print axioms` lines only.
* `W2_stderr.log` (0 bytes) — the accepted build's stderr; this is the source of the "0 bytes" figure.
* `W2_build_errors.md` — verbatim error text of the three failed elaborations (builds 1–3).
