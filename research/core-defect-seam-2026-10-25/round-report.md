# Discharge of `DefectLaurentRepr` and a nontrivial 2-torsion Tate point

Date: 2026-10-25. Base branch:
`autonomous/primitive-deck-class-20261025` at
`956557d9a8c7a2ee2ea3de7589cf6bd26dab84fb`.

## What was a seam

`TateCurvesTheta.TateParameter.DefectLaurentRepr`
(`TateCurve/TatePointMem.lean`) was a conditional input: the Weierstrass defect
is represented off the `q`-orbit by a convergent, `q`-invariant two-sided
Laurent series. It fed `tatePoint_mem`, hence the Tate point map and everything
built on it.

## How it closes

`TateCurve/TatePointOnCurve.lean` proves the defect vanishes off the orbit from
the Eisenstein pair identities:

```text
tateDefect_eq_zero (h12 : (12 : K) ≠ 0) (hu : ∀ n, q^n * u ≠ 1) :
  tateDefect u = 0
```

Since the defect is identically zero off the orbit, the representing series can
be taken to be the **zero coefficient family**, and all three clauses of
`DefectLaurentRepr` follow (`defectLaurentRepr`). Consequently `tatePoint_mem'`
is unconditional and supplies the point-map membership argument.

The residual mathematics is the two divisor convolutions
(`Arithmetic/DivisorConvolution.lean`), not the Laurent representation.

## The 2-torsion point

For a square root `s` of `q` (`s ^ 2 = q`), `Boundary/KummerDoubleCover.lean`
proves

* `deck_sq_eq_one` : `tatePointHom s * tatePointHom s = 1`;
* `deck_sq_ne_one` : `tatePointHom s ≠ 1`.

The proof of nontriviality is `s ∉ qᶻ`: if `s = qⁿ` then `q ^ (2n) = q`, so
`q ^ (2n - 1) = 1`, contradicting `qᵐ ≠ 1` for `m ≠ 0`. The point is the
explicit `tatePoint s = (X s, Y s)` on the Weierstrass model
`y² + xy = x³ + a₄x + a₆`.

## Port

This branch previously lacked the entire `TateCurvesTheta.TateCurve` subtree,
`AnalyticQuotient.lean`, `Arithmetic/DivisorConvolution.lean`,
`QParameter/BaseChange.lean`, and the `Theta/{PuncturedProduct,WeightSpace}`
modules. They were imported from the pinned upstream tree
(`tate-curves-theta@d1fba94861c886b671f4137ab35e24b7474c9e00`) and adapted to the
current toolchain with definitionally equal renames only:

```text
if_pos -> ite_eq_left      if_neg -> ite_eq_right
if_true -> ite_true        if_false -> ite_false
dif_pos -> dite_eq_left    dif_neg -> dite_eq_right
```

These are plain aliases in this Lean core; the renames change no statement and
no proof term. One proof was reshaped without changing its term
(`TateCurve/Quotient.lean`: `rw [...]; exact one_mul _` instead of one `rw`), and
the ported library disables only the style linter `linter.style.haveILetI`,
with `-DwarningAsError=true` still in force.

## Verification

```powershell
cd candidates/core-kummer
lake build Boundary.KummerDoubleCover
lake env lean -DwarningAsError=true Boundary/KummerDoubleCover.lean
```

Result: `Build completed successfully (8810 jobs)`. The five `#print axioms`
lines report exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`,
no custom axiom. Independent review additionally audited the upstream chain
(`defectLaurentRepr`, `tateDefect_eq_zero`, `tatePoint_mem'`, `tatePointHom_ker`,
the bracket identities) and reproduced the divisor-sum identities numerically
for `N < 200`.

## Honest boundaries

- The seam did not evaporate from the interface: `tatePoint` still takes its
  membership argument explicitly, and `memArg` fills it from `tatePoint_mem'`.
  What changed is that `memArg` is a definition proved from a theorem, not an
  assumed seam.
- `TameResidueChar K` is `‖2‖ = 1 ∧ 12 ≠ 0`, so **characteristic 2 is excluded**;
  the 2-torsion statement is not asserted there.
- Analytic Tate model only: no tempered covering, no `Π^tp_Y`, no line bundle
  `L_N`, no section `s₁`, no trivialization `τ_N`, no original IUT
  double-isogeny comparison, no editor or fact-tree admission.
- The port is an integration of pinned upstream work; the seam discharge itself
  is not new mathematics relative to that upstream tree.
