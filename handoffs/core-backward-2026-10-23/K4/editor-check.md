# K4 — three-gate record

Status: **verified in both planes** (CLI + editor, including Infoview zero-goal). The core GAP stays OPEN.

Deliverable: `candidates/core-transport/ExecutionProvenance.lean`
sha256 `f37a80d6de6872f5ed0a23d9f39c9557a79de8cc5cd05110c148c74d79c53543`, 208 lines, 11 declarations.

## What K4 had to fix

`handoffs/core-backward-2026-10-23/M3/` audited 11 interfaces of `external/iut` and found that **none**
requires an output to be produced by a legal execution: `out` is a bare structure field and
`realisation` only says *where* outputs land. A landing condition cannot determine a value — the log
image alone is a whole ball (`logImage_Q3_eq_closedBall`). K4 therefore makes provenance a type:

```
structure LegalExecution where
  input      : ℚ_[3]
  mem        : ‖input - 1‖ < 1
  steps      : ℕ → ℚ_[3]
  steps_eq   : steps = algorithmRun input     -- the trace IS the algorithm, definitionally
  value      : ℚ_[3]
  converges  : Tendsto steps atTop (𝓝 value)
```

`value_eq_localLog : e.value = localLog e.input` is then *derived* from `converges`, `steps_eq` and the
existing `Q_3` convergence theorem by uniqueness of limits, and `value_unique` says the value is a
function of the input alone. `value_mem_logImage` is a consequence here, not a hypothesis.

**Honest scope.** The algorithm is the p-adic logarithm's partial-sum algorithm on `ℚ_[3]`, **not** the
η-algorithm of IUT. Nothing here constructs a Θ-link, an `Ism` or Cor 3.12, and no audited interface has
been recast in provenance form. The file says all of this in its own module docstring.

## Gate 1 — CLI

```
cwd   candidates/core-transport
argv  lake env lean -DwarningAsError=true ExecutionProvenance.lean
exit  0            stderr 0 bytes
```

Re-checked independently on the final file (`f37a80d6…`) with the strict checker
(`cdsa/checks/check_lean_candidate.py --build-lib CoreTransport --require-all-axioms`):
**PASS** — 11 declarations, 0 errors, 0 warnings, 10 theorems each carrying an axiom report, no
forbidden terms, no axiom outside `{propext, Classical.choice, Quot.sound}`.

The first CLI run happened at 09:21:53, but the file was last touched at 09:22:25 (one docstring
reworded because it contained an `admit` substring). The gate was therefore **re-run** on the final
hash rather than carried over; that is the run recorded here.

## Gate 2 — editor diagnostics

VS Code 1.143.0, `leanprover.lean4-0.0.240`, trusted workspace `candidates/core-transport`,
`ExecutionProvenance.lean` open:

| severity | count |
|---|---|
| errors | **0** |
| warnings | **0** |
| information | 14 (4 from the neighbouring `DelegatedLogBridge.lean` + 10 from this file's `#print axioms`) |

Status bar: `信息: 14 条`, with no error or warning counter. Capture:
`editor/vscode-observation-tree-2.txt`.

## Gate 3 — Infoview zero-goal

Method: `--force-renderer-accessibility` (the Infoview is a webview; plain UI Automation cannot see it),
cursor parked after the last tactic step of each proof, polling the Tactic state section.

| declaration | line | reading |
|---|---|---|
| `algorithmRun_eq_partialSums` | 64 | `No goals` |
| `localLog_eq_padicLog` | 79 | `No goals` |
| `hasSum_logTerm_localLog` | 87 | `No goals` |
| `value_eq_localLog` | 138 | `No goals` |
| `value_unique` | 145 | `No goals` |
| `value_mem_logImage` | 155 (end of the proof line) | `Goals accomplished!` |
| `logImage_Q3_eq_closedBall` | 170 | `No goals` |
| `norm_four_sub_one` | 176 | `No goals` |
| `witnessFour` | 190 | `No goals` |

One honest wrinkle: the blank line after `value_mem_logImage` (156) read empty twice, so the reading was
taken at the end of the proof line itself (155), which is the same criterion. The other eight were read
at the blank line following their last tactic.

## What this does not establish

That a provenance-typed interface *can* be written on one concrete example, and that such an interface
determines its value. It does not show the η-algorithm, any IUT interface, a Θ-link, `Ism`, Cor 3.12, or
any degree/localization statement. `fact_tree_admitted` is `false` and the core GAP remains OPEN.
