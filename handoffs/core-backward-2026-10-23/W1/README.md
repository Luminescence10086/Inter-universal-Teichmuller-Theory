# W1 — reading invariance toy (`ReadingInvariance.lean`)

Task: W1 of the backward plan (`research/core-backward-2026-10-23/h1-decision.md`, §结论一′, and the
obligation it records).

## Scope

One new Lean file, **new** (it did not exist before this task; verified absent before writing):

* `candidates/core-transport/ReadingInvariance.lean` — namespace `ReadingInvariance`, 166 lines.
* No existing file was modified. Nothing in `tools/`, the fact-tree, the registry, or any other
  candidate was touched.

The file formalises one shape and only that shape: **the reading is invariant under a change of the
presentation, while the partial reading is not.**

* presentation = the enumeration of the algorithm's steps, i.e. `σ : Equiv.Perm ℕ` acting on the step
  index of the logarithm series on `ℚ_[3]`;
* reading = the unconditional series sum (`tsum`), identified with `CoreTransport.localLog`;
* partial reading = the finite partial sum along the enumeration (`partialSumAlong`).

**It is an analogue of Ind1–Ind3, not Ind1–Ind3.** The permutation group stands in for the change of
presentation that `(n,◦)` is subject to ("determined, **up to isomorphism**, by the various
`n,m`-theaters", source txt lines 8869–8873 as quoted in `h1-decision.md`); `tsum` stands in for the
reading. No Θ-link, `Ism`, prime-strip, Frobenioid, Hodge theater, coricity, or Galois action occurs in
the file, and no claim is made about any of them. This is stated in the module docstring in exactly
those terms.

## Contents (what each declaration does)

| declaration | role |
|---|---|
| `localLog_eq_padicLog` | `CoreTransport.localLog = PadicLogVolume.padicLog` by unfolding both; bridge only, no mathematical content (same statement as in `ExecutionProvenance.lean`). |
| `hasSum_logTerm_localLog` | the existing convergence theorem, **quoted** (`CoreLog.principal_unit_log_hasSum`); convergence is not re-proved. |
| `partialSumAlong σ x n` | the algorithm run in the order given by `σ`: `∑ k ∈ Finset.range n, logTerm x (σ k)`. |
| `partialSumAlong_one` | the one-step partial sum is the term the presentation picks first. |
| `hasSum_perm` | **item 2** — the sum over *any* enumeration is `localLog x`, from `Equiv.hasSum_iff` applied to the quoted unconditional convergence. |
| `reading_independent_of_enumeration` | **item 3** — two enumerations, one reading; both sides kept literally as `∑'`, so the statement is about the presentations rather than about `localLog` by construction. |
| `logTerm_four_zero`, `logTerm_four_two`, `norm_nine` | the three computed facts used by the counterexample. |
| `partialSum_not_invariant` | **item 4, the point of the file** — a concrete failure of invariance for the partial reading. |

### Item 4: the concrete counterexample

`σ = Equiv.swap 0 2` (the transposition `0 ↔ 2`), `n = 1`, at `x = 4 : ℚ_[3]`:

* `partialSumAlong (Equiv.swap 0 2) 4 1 = logTerm 4 2 = (-1)^2·(4-1)^3/3 = 27/3 = 9`;
* `partialSumAlong (1 : Equiv.Perm ℕ) 4 1 = logTerm 4 0 = 4 - 1 = 3`.

Separation: `‖9‖ = (9:ℝ)⁻¹ = 1/9` while `‖3‖ = 1/3` (`norm_nine`, `CoreLog.norm_three`), so
`9 ≠ 3` in `ℚ_[3]`. The witness is an actual `∃ σ n, …` with an explicit `σ` and `n`, **not** the
weaker `¬ ∀ σ n, …`.

## Commands

From `candidates/core-transport` (toolchain `leanprover/lean4:v4.34.0-rc2`, `lake-manifest.json` unchanged):

```
lake env lean -DwarningAsError=true ReadingInvariance.lean
```

Result: **exit code 0**, `-DwarningAsError=true`, stderr **0 bytes** (full log `W1_build_2.log`,
1998 bytes = the 10 `#print axioms` lines only). One repair round was needed
(`W1_build_1.log`: `Function.comp_apply` → `Function.comp_def`, since the goal was at the function
level rather than at an applied occurrence).

`lake update` was not run; Mathlib was not rebuilt; `lake build CoreTransport` was not needed since no
existing module was touched.

## Per-theorem axioms

Every declaration was printed with `#print axioms`; all ten lines are verbatim:

```
'ReadingInvariance.localLog_eq_padicLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.hasSum_logTerm_localLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.partialSumAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.partialSumAlong_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.hasSum_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.reading_independent_of_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.logTerm_four_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.logTerm_four_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.norm_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingInvariance.partialSum_not_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All lie in `{propext, Classical.choice, Quot.sound}`. No `sorry`, `admit`, `axiom` declaration,
`opaque`, or `native_decide` occurs; a case-insensitive scan of the whole file (docstrings included)
returns 0 hits for each of `sorry`, `admit`, `opaque`, `native_decide`, and `axiom` occurs only in the
ten required `#print axioms` commands.

## File identity

```
sha256  C9CB9BCDD40C3DCD3CF1C1C9E2012CF7A9250792410B7B7E09A010C94F16050B
bytes   9595
lines   166
```

## Mathlib lemma used for permutation invariance

`Equiv.hasSum_iff : HasSum (f ∘ e) a ↔ HasSum f a` — the `@[to_additive]` form of
`Equiv.hasProd_iff`, `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:183`. On the `tsum` side the
proof uses its companion `HasSum.tsum_eq` (additive form of `HasProd.tprod_eq`, `.../InfiniteSum/Defs.lean:332`);
`Equiv.tsum_eq` exists as well but was not needed. (This Mathlib has no `tsum_perm` / `HasSum.perm`.)

## What this does NOT establish

* It does not formalise Ind1–Ind3, the Θ-link, `(n,◦)`, the environment category, the formal quotient,
  or any other H1 object; it is a toy on `ℚ_[3]` only.
* It does **not** discharge the invariance obligation of §结论一′ for the real object. It shows the
  *shape* — invariant reading, non-invariant partial reading — is consistent and provable on one
  concrete complete field; nothing here transfers to `F⊩▶×μ`-prime-strips.
* It does not show that `tsum` is the right reading for the real object, nor that the enumeration model
  of "presentation" captures `up to isomorphism`. The permutation group is an **analogue** of the
  change of presentation, no more.
* It is not evidence for or against any IUT claim, and it does not touch the 11 audited interfaces of
  `handoffs/core-backward-2026-10-23/M3/` (it only records, in the docstring, that none of them
  carries the invariance).
* Convergence on the principal-unit domain is taken from `CoreLog`, not established here; the file
  proves nothing new about the logarithm itself.

## Logs

* `W1_build_1.log` — first attempt, exit 1, the single type-mismatch error (kept for provenance).
* `W1_build_2.log` — accepted build, exit 0, the ten `#print axioms` lines.
* `W1_stdout.log` (1998 bytes) / `W1_stderr.log` (0 bytes) — the accepted build with the two streams
  captured separately, which is where the stderr byte count comes from.
