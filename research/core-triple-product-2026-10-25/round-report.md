# Unconditional Jacobi triple product: verified upstream integration

Date: 2026-10-25. Base branch:
`autonomous/local-deck-synchronization-20261025` at
`ac91c3c3943d94c55a06cab622bc2f45d18dc342`.
Pinned upstream source:
`tate-curves-theta@d1fba94861c886b671f4137ab35e24b7474c9e00`.

## Headline

For a Tate parameter over any complete nonarchimedean normed field `K`, the
naive theta series and its product form are equal:

```text
TateCurvesTheta.TateParameter.theta_eq_thetaProd :
  ∀ (t : TateParameter K) (u : Kˣ), t.theta u = t.thetaProd u
```

and the zero divisor is the `qᶻ`-orbit of `-1`:

```text
TateCurvesTheta.TateParameter.theta_eq_zero_iff :
  t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k
```

No `LaurentCoeffUnique`, `ThetaProdLaurentRepr`, `RatioLaurentRepr` or
normalization hypothesis remains. The module docstrings that still described
these as open seams were updated to point at the closing modules; no theorem
statement was weakened.

## Imported proof chain

The third breakthrough is an integration of the fixed upstream proof, not a
new proof of the Jacobi triple product. The following seven files were copied
byte-for-byte from the pinned upstream tree and added as Lake roots:

1. `TateCurvesTheta/Theta/QBinomial.lean`
2. `TateCurvesTheta/Theta/FactorSeries.lean`
3. `TateCurvesTheta/Theta/Divisor.lean`
4. `TateCurvesTheta/Theta/ThetaProdLaurent.lean`
5. `TateCurvesTheta/Theta/ThetaProdGlobalLaurent.lean`
6. `TateCurvesTheta/Theta/Normalization.lean`
7. `TateCurvesTheta/Theta/Durfee.lean`

The chain closes two formerly explicit seams:

- `laurentCoeffUnique` is a theorem in `LaurentUnitSphere`, from the
  two-sided Strassmann sphere theorem;
- `thetaProdLaurentRepr` is a theorem in `ThetaProdGlobalLaurent`, from the
  Euler q-binomial expansion and the nonarchimedean Cauchy product.

`Durfee` then proves the Durfee-square scalar identity
`thetaProdNormConst = 1` by a dominated limit of the finite q-Vandermonde
identity, and the headline follows from `Normalization`.

## Verification

From a fresh clone of the branch, under the package configuration with
`-DwarningAsError=true`:

```powershell
cd candidates/core-kummer
lake build TateCurvesTheta.Theta.Durfee
lake build TateCurvesTheta.Theta.AuditTripleProduct
```

Results:

- `Durfee` chain plus audit: `Build completed successfully (2760 jobs)`.
- `AuditTripleProduct` adds explicit `#print axioms` for the headline,
  normalization, global Laurent representation, coefficient uniqueness and
  Euler expansion. The printed sets are only
  `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` and no custom
  axiom appears.

The repository still uses a machine-local absolute Mathlib path in
`lake-manifest.json`; this is inherited from the existing package and is a
reproducibility limitation, not a proof dependency.

## Independent adversarial reviews

Three independent workflow reviewers were run against the port:

1. **Mathematical falsifier.** Attacked the Durfee limit, Gaussian-binomial
   bound, q-Pochhammer identities, normalization and possible circularity;
   found no counterexample. Verified the headline has no residual
   `LaurentRepr` or `Card` premise.
2. **Provenance and axiom auditor.** Compared all seven files byte-for-byte
   with the pinned upstream; all identical. Found no `sorry`, `admit`, custom
   axiom, `native_decide` or `unsafe`. Correctly flagged that the new layer
   lacked explicit `#print axioms`; this report's `AuditTripleProduct` file
   was added in response.
3. **Integration auditor.** Checked the import closure, Lake roots and
   declaration uniqueness. Confirmed `Durfee` is reachable from the declared
   root and that the old conditional seams are discharged inside the branch,
   not stored in a structure field.

## Boundaries

- This is a **verified port/integration** of the pinned upstream proof, not a
  claim of a new mathematical discovery.
- It does not construct the original tempered line bundle, `s₁`, `τ_N`, root
  torsors, primitive deck generator, canonical cusp chart or any Θ-link data.
- It does not solve Corollary 3.12, (9-1) or abc.
- No VS Code editor observation was made, and no fact-tree or central
  registry entry is claimed.
- The result is a statement about the analytic Tate theta function and its
  divisor; it is a genuine source-level closure for the theta function, but
  not a reconstruction of the IUT comparison.
