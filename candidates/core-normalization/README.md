# Relative determinant normalization candidate

`RelativeDeterminant.lean` proves finite matrix, weighted determinant-line, positive-power and torsion-scalar identities over a normed field, with an actual Q₃ sign/ball calibration. Source motivation: IUT III Remark 3.1.1(iv), Remark 3.9.5(vii) Ob3/Ob4. It is not an original IUT object/measure realization.

Run from `../core-compactness`:

```powershell
lake env lean -DwarningAsError=true ../core-normalization/RelativeDeterminant.lean
```

Uses the already pinned local Mathlib / Lean 4.34.0-rc2. Final CLI output: `last-build.log`; receipt: `verification.json`. VS Code observation pending; fact-tree admission false. Full scope and next obligations: `../../research/core-normalization-attack-2026-10-23.md`.
