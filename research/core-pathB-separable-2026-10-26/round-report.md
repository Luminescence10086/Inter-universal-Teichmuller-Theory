# Path B: the Kummer polynomial is irreducible, finite and separable

Date: 2026-10-26. Base branch: `autonomous/pathB-kummer-algebra-20261026` @ `0492134`.

## Result

`candidates/core-kummer/Boundary/KummerFiniteEtale2.lean` proves, for
`t : TateParameter K` over a `NormedField K`:

* `kummerPoly_irreducible` : `X^2 - q` is irreducible when `q` is not a square;
* `kummer_finite` : `AdjoinRoot (X^2 - q)` is a finite `K`-module;
* `kummer_finrank` : its `K`-dimension is `2` when `q` is not a square;
* `kummerPoly_separable` : `X^2 - q` is separable when `q` is not a square and
  `2 != 0` (the derivative is `2X`).

Four of the five algebraic ingredients of a finite separable quadratic cover are
therefore in place.

## Not proved: formal etaleness

`Algebra.FormallyEtale K (AdjoinRoot (X^2 - q))` is **not** proved. The natural
route `Algebra.FormallyEtale.of_isSeparable` needs an `Algebra.IsSeparable`
instance; the available automatic instance (`Algebra.IsSeparable.of_integral`)
requires `CharZero K`, which is stronger than `2 != 0` and would silently change
the hypothesis. The correct route is `minpoly` computation via
`AdjoinRoot.minpoly_root`; that was attempted and not completed, so the claim is
withheld rather than weakened.

## Boundaries

- Algebra only: no `Spec R`, no `R[t]/(t^2 - (x - e))`, no scheme-theoretic finite
  etale cover.
- No comparison with the original IUT double isogeny
  (`TemperedFundamentalGroups.Andre.TateObjectDouble` is absent locally).
- No editor observation, no fact-tree admission.

## Verification

```powershell
cd candidates/core-kummer
lake build Boundary.KummerFiniteEtale2
```

`Build completed successfully (3252 jobs)`; four `#print axioms` lines, all
`[propext, Classical.choice, Quot.sound]`.
