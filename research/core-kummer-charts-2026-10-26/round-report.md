# The two Kummer charts of the Tate double cover (model level)

Date: 2026-10-26. Base branch: `autonomous/kummer-double-cover-20261025` at
`69f6568957ca7e0d944f250b84e2bcfb5eaf8dc7`.

## What is proved

The double cover of the étale theta construction is the `2`-isogeny
`E_{\sqrt q} \to E_q`, presented scheme-theoretically as
`X' = R[t]/(t^2 - (x - e))`. In the analytic Tate model the cover is the squaring
map on the multiplicative coordinate, and a square root `s` of `q` gives the two
charts

```text
chart+ : v |-> s * v,        chart- : v |-> -s * v.
```

`candidates/core-kummer/Boundary/KummerCharts.lean` proves:

* `chartPlus_sq`, `chartMinus_sq` : both charts have square `q * v^2` in the
  `u`-coordinate, so they are two lifts of the same point of the quotient;
* `chartPlus_neg` : the two charts are exchanged by the overlap change
  `v |-> -v`;
* `chart_eq_or_neg` : conversely, in a field any `w` with `w^2 = q v^2` is
  `s v` or `-s v` — the fibre of the squaring chart has exactly two points.

Boundary: the two preimages of `q v^2` are `(s v)^2`-roots, i.e. `± s v`; this is
the `K`-side of the two charts. It does **not** say that `-s v` is the Tate point
`-P_s`: negation on `E_q` is `tatePoint_inv` (`u |-> u^{-1}`), which is a different
involution. An earlier draft of this module claimed `chartMinus s v` equals the
negative Tate point; that claim is **false** and was removed before any commit.

## Why this is the honest form of the two charts

`-s v` and `s v` are distinct whenever `s v` is not 2-torsion, and they are the two
roots of the same quadratic. Packaging them as two charts of the Kummer cover is
therefore correct without pretending to build `R[t]/(t^2-(x-e))`.

## Verification

```powershell
cd candidates/core-kummer
lake build Boundary.KummerCharts
```

Result: `Build completed successfully (8811 jobs)`. The four `#print axioms` lines
report exactly `[propext, Classical.choice, Quot.sound]`.

## Boundaries

- Analytic Tate model only: no `R[t]/(t^2-(x-e))`, no tempered cover `Yddot`, no
  `Pi^tp_Y`, no `L_N`/`s1`/`tau_N`.
- No comparison with the original IUT double isogeny: the dependency
  `TemperedFundamentalGroups.Andre.TateObjectDouble` does not exist locally.
- No editor observation, no fact-tree admission.
