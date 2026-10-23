# W1 — three-gate record

Status: **verified in both planes**. This is an *analogue* of Ind1–Ind3, not Ind1–Ind3; the core GAP stays OPEN.

Deliverable: `candidates/core-transport/ReadingInvariance.lean`
sha256 `c9cb9bcdd40c3dcd3cf1c1c9e2012cf7a9250792410b7b7e09a010c94f16050b`, 166 lines.

## What W1 has to do, and what this file does

`research/core-backward-2026-10-23/h1-decision.md` §结论一′ quotes the source (txt 8869–8873): `n,◦HT`
is "determined, **up to isomorphism**, by the various `n,m`-theaters". An object determined only up to
isomorphism has no canonical presentation, so any reading built on it must be proved independent of the
presentation — and none of the 11 audited interfaces carries that invariance (M3: F3 false for all).

The file formalises that shape on `ℚ_[3]`:

| statement | content |
|---|---|
| `hasSum_perm` | for `‖x-1‖<1`, summing the algorithm's terms in **any** enumeration `σ` still sums to `localLog x` |
| `reading_independent_of_enumeration` | two presentations `σ`, `τ` give the same `tsum` — both sides kept literally as `tsum`s, so the statement is about the presentations |
| `partialSum_not_invariant` | **anti-degeneracy**: the *partial* reading is not invariant — concrete witness `σ = swap 0 2`, `n = 1`, `x = 4`, giving `9` versus `3`, separated by `‖9‖ = 1/9 ≠ 1/3 = ‖3‖` |

The substance is the third line: it is what forbids taking "the reading" to be a partial sum. The first
two quote `Equiv.hasSum_iff` (`HasSum (f ∘ e) a ↔ HasSum f a`, the additive form of
`Equiv.hasProd_iff`, `InfiniteSum/Basic.lean:183`) on top of the existing convergence theorem; no
convergence is re-proved, and no `tsum_perm`/`HasSum.perm` exists in this Mathlib.

**Honest scope.** The presentation here is the enumeration of the algorithm's steps; Ind1–Ind3 concern
Θ-link indeterminacies. Nothing here constructs a Θ-link, `Ism`, prime-strip, Frobenioid, Hodge theater,
coricity or Galois action. The file also does not discharge §结论一′ for the real object — it shows the
shape is consistent and provable, nothing more. `reading_independent_of_enumeration` permutes only the
enumeration at a fixed `x`; it does not prove independence of the choice of `x`.

## Gate 1 — CLI

```
cwd   candidates/core-transport
argv  lake env lean -DwarningAsError=true ReadingInvariance.lean
exit  0            stderr 0 bytes (stdout = the ten #print axioms lines)
```

Independent strict re-check (`cdsa/checks/check_lean_candidate.py --build-lib CoreTransport
--require-all-axioms`): **PASS** — 10 declarations, 0 errors, 0 warnings, every theorem carries an axiom
report, axioms only `{propext, Classical.choice, Quot.sound}`, no forbidden terms.

The builder reports one repair round (`Function.comp_apply` → `Function.comp_def`); the failed log is kept
as `W1/W1_build_1.log`, the passing one as `W1_build_2.log`.

## Gate 2 — editor diagnostics

Trusted workspace `candidates/core-transport`, `ReadingInvariance.lean` open, VS Code 1.143.0 +
`leanprover.lean4-0.0.240`:

| severity | count |
|---|---|
| errors | **0** |
| warnings | **0** |
| information | 24 (4 from `DelegatedLogBridge.lean`, 10 from `ExecutionProvenance.lean`, 10 from this file) |

Status bar: `信息: 24 条`, no error or warning counter. Capture:
`editor/vscode-observation-tree-2.txt`.

## Gate 3 — Infoview zero-goal

| declaration | line | reading |
|---|---|---|
| `localLog_eq_padicLog` | 66 | `No goals` |
| `hasSum_logTerm_localLog` | 75 | `No goals` |
| `partialSumAlong_one` | 87 | `No goals` |
| `hasSum_perm` | 100 | `No goals` |
| `reading_independent_of_enumeration` | 108 | `No goals` |
| `logTerm_four_zero` | 115 | `No goals` |
| `logTerm_four_two` | 120 | `No goals` |
| `norm_nine` | 127 | `No goals` |
| `partialSum_not_invariant` | 152 | `No goals` |

## A tool defect found and fixed while doing this

The first editor attempt for this file was **refused** (exit 3) because a freshly launched VS Code window
is titled just "Visual Studio Code" until the folder loads. While fixing that, I found a worse problem:
`capture-vscode-2.ps1` had once been patched through `Get-Content`/`Set-Content`, which double-encoded its
Chinese UI patterns into mojibake — so its restricted-mode check could silently report a restricted window
as trusted.

Both are fixed: the script now waits for the folder name in the title, and every localised UI pattern is
written as a `\uXXXX` regex escape in an ASCII-only file.

Effect on earlier receipts: the T3 and K4 editor captures predate the fix. Their trust evidence is not the
string match but the **presence of the Lean 4 status item and the InfoView**, both of which restricted mode
suppresses — so those observations stand, but the trust check inside the old script was unreliable and is
now repaired. This note exists so a later reader does not have to guess which version produced which
receipt.
