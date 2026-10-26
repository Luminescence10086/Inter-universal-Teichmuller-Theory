# Path B: the Kummer cover algebra is finite of degree 2

Date: 2026-10-26. Base branch: `autonomous/kummer-charts-20261026` @ `d905f88`.

## Result

Path B asks for the finite étale cover built from a real 2-torsion point. The
algebraic core is the Kummer algebra `K[t]/(t^2 - q)`.
`candidates/core-kummer/Boundary/KummerFiniteEtale.lean` proves:

* `kummerPoly_irreducible` : `X^2 - q` is irreducible when `q` is not a square;
* `kummer_finite` : `Module.Finite K (AdjoinRoot (X^2 - q))`, for every Tate
  parameter (this is the "finite" of finite étale);
* `kummer_finrank` : when `q` is not a square, the extension has `K`-dimension 2.

## What is deliberately not claimed

* **Étaleness / separability is not proved here.** `X^2 - q` is separable iff
  `2 != 0`, and the module does not assert `Algebra.FormallyEtale`; that step needs
  a `NeZero (2 : K)` hypothesis and a separability lemma whose Mathlib name must be
  checked. Claiming "finite étale" without it would overstate the result.
* **No scheme, no `Spec R`, no `R[t]/(t^2 - (x - e))`.** The algebra here is the
  analytic Tate model's Kummer algebra, not the geometric finite étale level.
* **No comparison with the original IUT double isogeny.** `TemperedDouble` needs
  `TemperedFundamentalGroups.Andre.TateObjectDouble`, which does not exist locally.
* No editor observation, no fact-tree admission.

## Verification

```powershell
cd candidates/core-kummer
lake build Boundary.KummerFiniteEtale
```

`Build completed successfully (2939 jobs)`; the three `#print axioms` lines report
`[propext, Classical.choice, Quot.sound]`.
