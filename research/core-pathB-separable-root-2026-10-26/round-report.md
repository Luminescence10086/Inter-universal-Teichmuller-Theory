# Path B: the adjoined Kummer root is separable

Date: 2026-10-26. Base branch: `autonomous/pathB-separable-20261026` @ `c4abee5`.

## Result

`candidates/core-kummer/Boundary/KummerIsSeparable.lean` proves:

* `minpoly_kummerRoot` : `minpoly K (root (X^2 - q)) = X^2 - q` (the polynomial is
  monic, so its leading-coefficient factor is trivial);
* `isSeparable_kummerRoot` : the adjoined root is a separable element over `K`,
  when `q` is not a square and `2 != 0`.

## Not proved: `Algebra.IsSeparable` for the whole algebra

The step from "the generator is separable" to
`Algebra.IsSeparable K (AdjoinRoot (X^2 - q))` was attempted via
`IntermediateField.isSeparable_adjoin_simple_iff_isSeparable` plus
`adjoinRootEquivAdjoin` and via `AlgEquiv.Algebra.isSeparable`. Both attempts failed
on elaboration (`K⟮root⟯` notation and the `AlgEquiv` transport direction), so the
statement is withheld rather than weakened or faked with `sorry`.

The honest current status of Path B's algebraic layer:

| ingredient | status |
|---|---|
| `X^2 - q` irreducible when `q` not a square | proved |
| finite `K`-module | proved |
| `K`-dimension 2 | proved |
| `X^2 - q` separable when `2 != 0` | proved |
| root is a separable element | proved |
| `Algebra.IsSeparable` for the algebra | **not proved** |
| `Algebra.FormallyEtale` | **not proved** |

## Boundaries

- Algebra only; no `Spec R`, no geometric `R[t]/(t^2-(x-e))`, no tempered cover.
- No comparison with the original IUT double isogeny.
- No editor observation, no fact-tree admission.

## Verification

```powershell
cd candidates/core-kummer
lake build Boundary.KummerIsSeparable
```

`Build completed successfully (3253 jobs)`; two `#print axioms` lines, both
`[propext, Classical.choice, Quot.sound]`.
