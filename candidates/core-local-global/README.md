# Fixed-native local-global representation prototype

## Same-lattice stabilization and saturation addition

Current receipt: `stabilizer-saturation-verification.json`; log: `stabilizer-saturation-build.log`. `LatticeStabilizer.lean` constructs the integral inverse from same-full-lattice preservation over Q_p, in arbitrary fixed frames, and separates one-sided inequality from two-sided equality. `SaturationGrowth.lean` gives a finite F_3² regression: determinant-one images preserve individual size while saturation and a larger coefficient-ring ideal hull can grow. No original IUT instance or Haar lift is asserted. The latest receipt supersedes the earlier library-configuration pin; no fact-tree admission. See `../../research/lattice-stabilizer-saturation-2026-10-23.md`.

## Collections and integral character addition (2026-10-23)

This folder is now a standalone Lake project. `lake build CoreLocalGlobal` checks all declared root modules with warnings as errors. `Collections.lean` separates raw local categories from their realifications and constructs the forgetful functor, structure transport and exact lift criteria. `IntegralScalarOrbit.lean` gives a concrete integral-scalar category and its norm-classified arrow orbits. `IntegralMatrixCharacter.lean` constructs the determinant representation of actual GL_n(Z_p) and proves its zero real-log-norm character. These are candidates, not original IUT instances. Historical verification: `collections-integral-verification.json`; historical log: `collections-integral-build.log`. No new editor observation or fact-tree admission. Source scope and remaining obligations: `../../research/core-integral-realization-2026-10-23.md`.

This candidate implements structure rather than numerical comparison. It uses
actual Mathlib categories, functors, isomorphisms and morphisms. Its parameters
have not been instantiated by the original IUT construction.

## Data retained

For one fixed global object N, localization functors loc_i, and local targets H_i:

- `PolyHom X H` is a structure arrow X → H modulo postcomposition by an
  automorphism of H. It is an orbit of **arrows**, not a quotient of volumes.
- `NativeFiber` retains local objects X_i, isomorphisms X_i ≅ loc_i(N), and
  structure-arrow orbits X_i → H_i.
- `FiberHom` retains the commuting native localization squares and the structure
  orbits. Its base map on N is the identity: this is the strictly framed fiber.
- `FrameChange` separately allows one global automorphism of N with all its
  actual localizations. No independently selected local gauges are substituted.

`canonicalIso` constructs an actual isomorphism to a normal representation with
X_i = loc_i(N), retaining the normalized structure-arrow orbits.
`iso_nonempty_iff_normalized` identifies exactly when two strictly framed
representations are isomorphic. `frameChange_exists_iff` gives the corresponding
criterion when a common global change of frame is allowed.

## Descent is not a default field

`GloballyRealized` is an explicit *obligation* that the whole normalized family
comes from a single global morphism N → T. `ofGlobalArrow` constructs a represented
object from an actual global arrow, and `realizedFiber_exists_iff` exposes the
remaining global-arrow existence problem.

`local_representations_do_not_force_descent` supplies a categorical counterexample
to automatic descent. `constant_not_identity_poly` shows that even identical
underlying source/target objects can carry different structure-arrow orbits.
Neither example is an IUT counterexample.

## Exact semantic limits

To interpret the source's linear structure poly-morphisms, the chosen local
categories must encode the required linearity and equivariance, with actual
localization functors. No such IUT instance is supplied here. The global native
object may itself have to carry extra rigidification before these definitions
are appropriate; a q label alone does not provide it.

This construction models the structure-arrow orbit and a framed local-global
representation. It does not implement the entire formal/stack-theoretic quotient
of IUT III. In particular, it does not assert that source comparisons must descend
to a single ordinary global morphism. A degree-compatible comparison in the source's
formal quotient may instead be sufficient; that alternative remains open.

No degree equality, desired inequality, `Wall` or `h312` is assumed as a field.
There is also no proof of original algorithm admissibility or Corollary 3.12.

## Proof environment

`NativeFiber.lean` reuses the existing Lean 4.34.0-rc2 / cached Mathlib environment.
From `../core-compactness`:

```powershell
lake env lean -DwarningAsError=true ../core-local-global/NativeFiber.lean
```

The root project and the delegated M1–M4 outputs are untouched. Mathematical
development checks were performed here; packaging and editor admission remain
separate. See `verification.json` for the final recorded CLI result. No fact-tree
admission is claimed.
# IPL coherence addition (2026-10-23)

`IPLCoherence.lean` formalizes the arrow word in III Remark 3.11.1(iii), its explicit representative defect, and its reduction under the two commutative squares of Remark 3.10.2. It does not choose representatives in the original IUT poly-isomorphisms. Run from `../core-compactness` with `lake env lean -DwarningAsError=true ../core-local-global/IPLCoherence.lean`. Separate receipt: `ipl-verification.json`; log: `ipl-build.log`. CLI verified, editor observation pending, fact-tree admission false. This addition does not change the older `NativeFiber.lean` receipt.

