# W4 — gate record

Deliverable: `candidates/core-transport/TransitionCompatibility.lean`
sha256 `391bee2f83606ff4de4f8dbc905aceae052383efc5722baacc49e46250874b72`, 637 lines.
This file upgrades W2's toy localization (`global = local`) into **transitions with a cocycle law**.

## What the file does

`PresentationChain k` (`k ≥ 1`) carries `input : Fin k → ℚ_[3]` on the principal units and, for every
`i ≤ j`, a transition `step i j h : ℚ_[3] → ℚ_[3]` given by multiplication by a principal unit `unit`,
with `stepInv`, the isomorphism law `stepInv_step`, `unit_refl`, and `step_input` making the elementary
transitions `i → i+1` carry `input i` to `input (i+1)`. `IsCompatible` is the **cocycle law**
`unit i l = unit i j * unit j l` for `i ≤ j ≤ l` — a hypothesis, not a structure field.

The reading is `localLog` of the presentation, pushed back to the base frame by the inverse transition
(`relativeInput`); `reading_hasSum` and `reading_is_limit_of_algorithm` show it is the sum and the limit
of the algorithm's partial sums, and `relativeInput_mem` supplies the convergence hypothesis. From the
cocycle, `input_transport` (induction, one use of the law per step) gives `reading_eq_base`, hence
`reading_compatible : ∀ i j, reading i = reading j`.

**Anti-degeneracy**: `chainCompat` versus `chainBroken`, presentations `4, 16, 64`; the elementary units
are `4` in both chains while the comparison unit `0→2` is `16` versus `64`. `chainBroken_not_compatible`
(compatibility would force `64 = 16`), the readings at `0` and `2` differ, and
`difference_lies_in_the_direct_transition` shows the inputs and the elementary units agree — only the
direct transition differs.

**Design note recorded in the file**: on principal units multiplication is sharply transitive and `log`
injective, so requiring *every* transition to transport the presentation would force the comparison
units from the inputs, making the cocycle automatic and the equality true by construction. The file
therefore records elementary transports (structure) and comparison transitions (data) separately, and
says so.

## Gate 1 — CLI

```
cwd   candidates/core-transport
argv  lake env lean -DwarningAsError=true TransitionCompatibility.lean
exit  0            stderr 0 bytes
```

Strict re-check (`--build-lib CoreTransport --require-all-axioms`): **PASS** — 50 declarations,
0 errors, 0 warnings, 50 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`, no
forbidden terms.

The first strict run flagged **4 theorems without an axiom report** (`stepInv_step`,
`relativeInput_mem`, `reading_hasSum`, `reading_is_limit_of_algorithm`). That was an audit gap, not a
proof gap; the main line added the four `#print axioms` lines (fully qualified, since they live inside
`PresentationChain`), and no proof was touched. The resumed check passes and a planted-`sorry` negative
control still fails, so the repair did not blunt the gate.

## Gate 2 — editor

Trusted workspace, Lean 4 extension active, `TransitionCompatibility.lean` open: **0 errors,
0 warnings**, information entries present. Capture: `editor/vscode-observation-tree-2.txt`.

## Gate 3 — Infoview

Not attempted for this file. The three gates this batch asks for are the CLI, the axiom whitelist and
editor zero diagnostics, all recorded above.

## What it does not say

`Fin k` is an index set, not a set of places; the transitions are multiplication by powers of `4`, not
localization morphisms; and nothing here touches `⊼fQ₁`/`⊼fQ₂`, log-volumes, the Θ-link, `Ism` or
Cor 3.12. It is the shape "compatible transitions force equal readings, incompatible ones need not",
not IUT's localization data. Core GAP stays OPEN.
