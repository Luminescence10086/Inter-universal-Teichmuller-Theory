# W5 — gate record

Deliverable: `candidates/core-transport/NormalizationAlignment.lean`
sha256 `03b6e50289e4150b8ef98537deab952b14f5e80b0d8ccdc850a8be8ee56b2412`, 406 lines, 31 declarations,
31/31 axiom reports.

## What it formalises

The H3 alignment obligation (see `research/core-backward-2026-10-23/h3-prerequisites.md`): the source's
procession normalization is an **average over the label orbit** `j in F_l^star`, while (xi-d) indexes by
`|F_l|` with the label `0` identified with `langle F_l^star rangle` (IUT II Cor 4.10(i)). The algebraic
content of that identification is: *for an invariant reading, averaging over the orbit equals the value at
the label*.

```
theorem average_eq_value_of_invariant (hf : Invariant f) (g : G) : orbitAverage f = f g
theorem alignment (hf : Invariant f) : orbitAverage f = f 1
```

## Gates

- CLI: `lake env lean -DwarningAsError=true NormalizationAlignment.lean` — exit 0, stderr 0 bytes.
  Independent strict re-check: **PASS** — 31 declarations, 0 errors, 0 warnings, 31 axiom reports,
  axioms only `{propext, Classical.choice, Quot.sound}`, no forbidden terms.
- Editor: trusted workspace, Lean 4 active — **0 errors, 0 warnings**, information entries present.
  Capture: `editor/vscode-observation-tree-2.txt`.
- Infoview: not attempted (the three gates for this batch are CLI, axiom whitelist, editor zero
  diagnostics).

## Anti-degeneracy

`LabelGroup = Equiv.Perm (Fin 2)`; a reading with values `5` at `1` and `7` at `swapLabels`; the orbit
average is `6 = (5+7)/2`, the value at the label is `5`, so `6 != 5`, and `not Invariant` is proved — the
hypothesis really fails. Non-vacuity: `invariant_const`, `orbitAverage_const`.

The file also discloses `invariant_iff_const` (on the self-action carrier, invariance *is* constancy)
rather than hiding it.

## What it does not say

It does not prove that (xi-d)'s `|F_l|` index *is* the procession average. It proves that for an invariant
reading, orbit-averaging and value-at-label coincide, so group-indexing and label-indexing agree at that
level; the source alignment remains a **definition alignment**, not a theorem of this file. Nothing here
touches Θ-links, `Ism`, log-volumes or Cor 3.12. Core GAP stays OPEN.
