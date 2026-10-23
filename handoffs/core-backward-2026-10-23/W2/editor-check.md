# W2 — gate record

Deliverable: `candidates/core-transport/CollectionProvenance.lean`
sha256 `cddea79c5df62cd2e3ad999206526d449434798fd741e7e5371e6150fa601422`, 526 lines, 32 declarations
with axiom reports.

## Gate 1 — CLI

```
cwd   candidates/core-transport
argv  lake env lean -DwarningAsError=true CollectionProvenance.lean
exit  0            stderr 0 bytes
```

Independent strict re-check (`--build-lib CoreTransport --require-all-axioms`): **PASS** — 33 declarations,
0 errors, 0 warnings, 32 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`, no forbidden
terms.

## Gate 2 — editor

Trusted workspace, Lean 4 extension active, `CollectionProvenance.lean` open:
**0 errors, 0 warnings**, information entries present (the axiom lines plus the neighbouring files').
Capture: `editor/vscode-observation-tree-2.txt`.

## Gate 3 — Infoview

Not run for this file. The goal for this item asks for CLI zero diagnostics, the axiom whitelist and
editor zero diagnostics; all three are recorded above. Infoview zero-goal readings were taken for the
other two toy files (K4, W1, W3) and are recorded in their own directories.

## What W2 establishes, and what it does not

The provenance type is lifted from a single element to a **local-global collection**: each local piece
carries `steps_eq : steps = algorithmRun input` (so its trace *is* the algorithm), the local reading is
derived by uniqueness of limits, and the global reading is tied to the local ones by a toy localization.
The anti-degeneracy statement took its preferred form: two collections with the same `n`, every local
value in the log image, and different global readings. The builder also recorded the sharper fact that
makes the stronger form impossible here — identical `localInput` forces identical readings.

Not established: the localization is a toy equality, not IUT localization data; the collection is a
`Fin n` family over `ℚ_[3]`, not an adelic or hull object; nothing here touches Θ-links, `Ism`,
prime-strips or Cor 3.12. Core GAP stays OPEN.
