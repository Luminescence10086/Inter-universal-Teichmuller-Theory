# W3 — gate record

Deliverable: `candidates/core-transport/DivideBackLaw.lean`
sha256 `904cbf9b8c6ff758744b66ee5cb8e80c18954dee6c5d7d7dc31bef5466d4c130`, 243 lines, 16 declarations
with axiom reports. Companion document: `research/core-backward-2026-10-23/h3-prerequisites.md`.

## Gate 1 — CLI

```
cwd   candidates/core-transport
argv  lake env lean -DwarningAsError=true DivideBackLaw.lean
exit  0            stderr 0 bytes
```

Independent strict re-check (`--build-lib CoreTransport --require-all-axioms`): **PASS** — 16 declarations,
0 errors, 0 warnings, 16 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.

History worth keeping: the first version I gated failed with **1 error, 1 warning and `sorryAx`**
(`L131` unused `hM`; `L203` `simpa` type mismatch). Both were reported back with the exact diagnostics and
fixed inside the agreed two rounds — the unused hypothesis was made genuinely load-bearing by deriving the
power law *from* `divide_back`, not by renaming it to `_hM`.

## Gate 2 — editor

Trusted workspace, Lean 4 extension active, `DivideBackLaw.lean` open:
**0 errors, 0 warnings**, information entries present. Capture: `editor/vscode-observation-tree-2.txt`.

## Gate 3 — Infoview

Ten of thirteen declarations read `No goals` / `Goals accomplished!` at the cursor position after the last
tactic: `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`, `divide_back`,
`localLog_pow_eq_smul`, `norm_four_Q3`, `norm_four_sq_Q3`, `norm_four_sub_one_Q3`,
`naive_magnitude_divide_back_fails`, `naiveDivideBack_four_two`.

Three were **not read**: `norm_pow_sub_one_lt_Q3`, `norm_two_Q3`, `divide_back_four_two`. The cause is my
own cursor-line helper (it computes the line after a block, and for these three it lands one or two lines
off, on a docstring or a blank line where the Tactic state section is empty). This is a capture-tool
limitation, not a Lean failure: all three carry axiom reports and the file compiles with zero diagnostics.

## What W3 establishes, and what it does not

On `ℚ_[3]`: `divide_back` recovers the logarithm reading of `x` from that of `x ^ M` by dividing by the
scalar `M`, derived from the quoted `PadicLogVolume.padicLog_pow`; and at the same `x = 4`, `M = 2` the
naive magnitude reading does **not** divide back (`1/2` against `1`), so "divide by `M`" is not a
content-free step.

Not established: `x ↦ x^M` is not `det^{⊗M}`, `ℚ_[3]` is not the localisation of an arithmetic line bundle,
and none of the three obligations in `h3-prerequisites.md` is discharged — the file gives the *shape* of
M-i only. `M-ii` and `M-iii` remain obligations. Core GAP stays OPEN.
