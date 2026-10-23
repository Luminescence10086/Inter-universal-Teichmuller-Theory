# M4 — SUMMARY (≤15 lines)

Static search of `external/iut` (HEAD `f7ed1cc8`, verified) + local Mathlib. 8 hits. No Lean, no build, no clone.

1. **Need 2 (group action + equivariant morphisms): covered.** `Iut.Frobenioid.OrbitObj`/`OrbitHom` (TemperedBase 43–55) = `B^temp(Π)⁰`; equivariance is a field, surjectivity/injectivity/FSM-bijectivity are proved theorems (87/163/178).
2. **Need 3 (poly-morphism/orbit data + allowed morphisms): partial.** Orbit category is concrete; allowed morphisms are `RlfMuStrip.Iso` / `ValBPS.Iso`. But "poly-morphism" is only reconstructed as "value part is a subsingleton" (`Iso.val_eq` 208, `isoEquivUnit` 214) — there is no poly-morphism type acting on pilots.
3. **Need 1 (local + global + localization isomorphisms): partial, reduced.** `RlfMuStrip` (PrimeStrip 159) encodes IUT II Def 4.9(viii) but its own docstring says `C^⊛` and the `ρ_v` are kept only through realified value groups + `localPilot`. The localization isomorphisms are **absent from the type**. No descent/gluing statement found.
4. **Need 4 (pullback/base-change preserves structure): the decisive negative.** In general it is an *assumed field* (`IsFrobenioid.pullback_surj`, Defs 250–252). Existence is proved only for model Frobenioids (`Model.isFrobenioid` 302; pullback literally built at 121–126) and degenerately for the angular one (Angular/Frobenioid 106). Nothing along the real IUT operations; nothing about descent to a quotient.
5. **Need 5 (determinant/tensor power + degree): split.** `abs_det_archIndMap` (GalKummerAll 327) proves `|det(⊗_j ψ_j)| = 1` — real-vector-space, ∞ only, no line/tensor-power degree formula. `degree_frobenius` (Global 328) is a **certificate-field projection**; `degree_hom` and the `Iut4Sec1` pullback degree pair (151/167) are genuine.
6. **Traps avoided:** (a) `pullback_surj`/`base_surj`/`frobenius` are fields of a Prop-structure, not theorems; (b) `degree_frobenius` extracts `Div φ = 0` from the supplied certificate; (c) structure-vs-existence separated per hit (`ValBPS` is not automatically inhabited; `qVal` supplies one); (d) a generic `HasLocalization` in Mathlib is category localization and does not apply here.
7. **Caveat:** local Mathlib is `85e3a25e`/Lean v4.34.0-rc2, the repo pins mathlib `v4.32.0` — do not reuse Mathlib names across the two revisions.

Details: `reuse.csv`, `missing.md`. Status `STATIC_ONLY`. No fact-tree, no repo edits.
