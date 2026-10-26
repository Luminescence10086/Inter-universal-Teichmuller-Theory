# Continuous Kummer comparison tools

Lean 4.34.0-rc2. From this directory: `lake build CoreKummer`.
Dependencies use the existing local Mathlib cache via path-only lake-manifest;
do not run `lake update` as part of a bounded replay.

The four ContinuousKummerTheory files are Apache-2.0 sources from
`https://github.com/lana-agents/continuous-kummer-theory`, commit
`98b67dfe9c82415aa17caa633d93960b6829af2e`, with four `haveI` to `have`
linter migrations. See LICENSE.upstream and
`research/core-kummer-2026-10-24/upstream-port.patch` from the repository root.

`ValuationSupport` compiles the neighboring
`core-local-global/KummerValuationSeparation.lean` without changing that
project's configuration. `KummerClassValuationBridge` consumes the genuine
Kummer kernel theorem. `CohomologyReflection` gives an explicitly conditional
injectivity criterion for the genuine continuous H1 map.

These are Qp/generic cohomological tools, not an instantiation of original IUT
tempered groups or a proof of Corollary 3.12/abc. Precise statements, source
audit, open obligations, build logs and editor evidence are recorded in
`research/core-kummer-2026-10-24/README.md`.

The next verified entry point is `Boundary/Frontier.lean`: general discrete
valuations, actual finite-place completions, finite normalization precision,
rational-point decomposition reflection and a concrete Laurent/power-series
germ consumer. See `research/core-boundary-2026-10-24/README.md` for exact
assumptions, replay instructions and editor evidence. The original Lake roots
remain unchanged; the new entry is compiled with `lake env lean` explicitly.
Do not import Frontier together with its source-section modules: they use the
same declaration names. This extension still does not reconstruct tempered Pi
or close the original IUT comparison.

## Annular deck-constant synchronization

`Boundary/LocalDeckSynchronization.lean` closes the per-annulus constant twist
question left open by the annular-descent round. It consumes the same-frame
closed q-annular atlas, its endpoint summability and sphere overlaps, one
nonzero local Laurent value, and local deck equations with **possibly different**
constants `α m`. It proves:

* `CoreLocalDeckSynchronization.constants_eq_succ` : `α (m + 1) = α m`;
* `constants_eq_zero` : every `α m` equals `α 0`;
* `global_twisted_law` / `exists_common_twist` : the common twist is an output,
  not a global input;
* `locally_twisted_curvature_eq_q` : `B 0 (n+2) * B 0 n / B 0 (n+1)^2 = q`.

`Boundary/SphereNonvanishing.lean` supplies the shared nonzero point from
sphere coefficient uniqueness; `Boundary/AnnularOverlap.lean` supplies the
q-annulus overlap geometry. The target is a Lake root:

```powershell
lake build Boundary.LocalDeckSynchronization
```

The minimal build from a clean checkout completes 2758 jobs with
`-DwarningAsError=true`; all seven new declarations print only
`propext`, `Classical.choice` and `Quot.sound`. No editor observation,
fact-tree admission, export bridge, original tempered realization, primitive
deck identification, Corollary 3.12 or abc claim is made here. The same-frame
and fixed Tate-coordinate hypotheses remain substantive inputs.

## Unconditional Jacobi triple product

`TateCurvesTheta/Theta/Durfee.lean` closes the product/series comparison for
the Tate theta function. Over every complete nonarchimedean normed field it
proves, with no normalization or Laurent-representation hypothesis left:

* `TateCurvesTheta.TateParameter.theta_eq_thetaProd` :
  `t.theta u = t.thetaProd u` for all `u : Kˣ`;
* `TateCurvesTheta.TateParameter.theta_eq_zero_iff` :
  `t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -q^k`.

The proof chain is the fixed upstream chain at
`tate-curves-theta@d1fba94861c886b671f4137ab35e24b7474c9e00`:
Euler q-binomial expansion (`FactorSeries`) → global nonarchimedean Laurent
convolution (`ThetaProdGlobalLaurent`) → Laurent coefficient uniqueness
(`LaurentUnitSphere`) → closed normalization (`Normalization`) → Durfee-square
identity (`Durfee`). The seven ported files retain the Apache-2.0 header and
`LICENSE.upstream`.

An explicit `#print axioms` audit is in
`TateCurvesTheta/Theta/AuditTripleProduct.lean`:

```powershell
lake build TateCurvesTheta.Theta.AuditTripleProduct
```

The port is a verified integration of the pinned upstream proof, not a claim
of new mathematics. No editor observation, fact-tree admission, original
tempered line-bundle realization, Corollary 3.12 or abc claim is made.

## Primitive deck action and the canonical cusp class

`Boundary/PrimitiveDeck.lean` builds the deck structure of the analytic Tate
coordinate model. It supplies a **model-level** primitive-deck result and a
**model-level** cusp class (it does not touch `L_N/s₁/τ_N`):


* `CorePrimitiveDeck.q_zpow_ne_one`, `zpow_injective`,
  `deck_generator_infinite_order` : `q` is not a root of unity, so `m ↦ qᵐ`
  is injective — the deck group of the model is generated by one element of
  infinite order (the primitive generator of *this* model);
* `deck_action_free` : `qᵐ · u = u` forces `m = 0`; the action is free;
* `deckOrbitEquiv` : every orbit is a concrete `ℤ`-torsor;
* `DeckQuotient` : the model quotient `Kˣ/qᶻ`, defined as a `Setoid` quotient
  (deliberately not called `E_q`; no Weierstrass structure is attached);
* `deck_automorphy` : the `qᶻ`-automorphy of `theta` is the deck law;
* `cuspClass` : the deck class of `-1`, proved by
  `theta_zero_iff_eq_cuspClass` to be the class where `theta` vanishes, and by
  `theta_zero_orbit_unique` to contain every zero — i.e. the zero locus is a
  single deck class.

```powershell
lake build Boundary.PrimitiveDeck
```

Recorded gap: `one_ne_neg_one` proves `(1 : K) ≠ -1` from `[CharZero K]`, but the
quotient-level distinctness `cuspClass ≠ [1]` is not proved here. Until it is,
`cuspClass` is the labelled zero orbit, not a separately certified second point.

Scope: this is the analytic-coordinate model. It does not construct the
tempered covering `Π^tp_Y`, the line bundles `L_N`, the section `s₁` or the
trivialization `τ_N`; those need a structure sheaf on infinite rigid-analytic
covers that the current dependency layer does not provide. It also does not
identify this model's `q` with the original IUT deck generator. See
`research/core-primitive-deck-2026-10-25/round-report.md`.

## Defect seam discharged; nontrivial 2-torsion Tate point

`TateCurvesTheta/TateCurve/TatePointOnCurve.lean` proves the Weierstrass
defect vanishes off the `q`-orbit (`tateDefect_eq_zero`), so the former
conditional seam `DefectLaurentRepr` holds with the zero coefficient family
(`defectLaurentRepr`) and `tatePoint_mem'` is unconditional.

`Boundary/KummerDoubleCover.lean` then proves that for a square root `s` of `q`
the Tate point of `s` is a nontrivial `2`-torsion point:

* `deck_sq_eq_one` : `tatePointHom s * tatePointHom s = 1`;
* `deck_sq_ne_one` : `tatePointHom s ≠ 1`.

```powershell
lake build Boundary.KummerDoubleCover
```

Boundaries: characteristic `2` is excluded (`TameResidueChar` requires
`‖2‖ = 1`); the membership argument is still an explicit parameter (`memArg`
fills it); analytic Tate model only, with no `L_N`, no `Π^tp_Y` and no original
IUT double-isogeny comparison. See
`research/core-defect-seam-2026-10-25/round-report.md`.
