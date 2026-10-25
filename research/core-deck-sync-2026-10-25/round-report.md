# Local deck-constant synchronization: verified candidate round

Date: 2026-10-25. Base commit: `f561e03363d26a785c17bba2ad39a4921a390ee2`.
This report describes a Lean CLI candidate result. It is not an editor
observation and not a fact-tree admission.

## Result

On one fixed Tate realization, suppose the closed q-annular atlas has:

- endpoint weighted summability at `q^(m+1)` and `q^(m-1)` for every `m : ℤ`;
- same-frame, same-coordinate overlap equality on every shared sphere;
- a local deck equation on each annulus with its own constant `α m : Kˣ`;
- at least one actual local point where the Laurent value is nonzero.

Then the constants are not independent:

```text
α (m + 1) = α m  for all m,
α m = α 0        for all m,
F(q u) = α 0 * (q u)⁻¹ * F(u)  for all u,
(B 0 (n+2) * B 0 n) / (B 0 (n+1)^2) = q  for all n.
```

The shared nonvanishing point is derived, not assumed. It follows from one
nonzero local value, `coefficient_families_eq`, and sphere coefficient
uniqueness. The zero-family case is excluded by that nonzero value; without
it the conclusion is false for arbitrary constants.

Main declarations:

- `CoreLocalDeckSynchronization.constants_eq_succ`
- `CoreLocalDeckSynchronization.constants_eq_zero`
- `CoreLocalDeckSynchronization.global_twisted_law`
- `CoreLocalDeckSynchronization.exists_common_twist`
- `CoreLocalDeckSynchronization.locally_twisted_curvature_eq_q`
- supporting `global_family_ne_zero`, `shared_nonzero_point`

Source: `candidates/core-kummer/Boundary/LocalDeckSynchronization.lean`.

## Verification

The candidate was replayed from a minimal fresh checkout containing only the
17 source files in the target import closure, the Lake root update, and the
existing package configuration.

```powershell
cd candidates/core-kummer
lake build Boundary.LocalDeckSynchronization
```

Result: `Build completed successfully (2758 jobs)`. The Lake root uses
`-DwarningAsError=true`. The recorded `#print axioms` output for all seven new
declarations is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, custom axiom, `native_decide`, or exported unsafe
declaration was found in the target import closure. `SphereNonvanishing`
previously carried a stale "pending parent Lean" line; it now records the CLI
status without claiming editor or fact-tree admission.

## Adversarial reviews

Three independent workflow reviewers were run against the candidate:

1. mathematical falsifier: attempted a concrete model with unequal `α m`;
2. index/dependency auditor: checked all integer shifts, negative indices,
   shared-annulus membership and the `m → 0` gluing;
3. proof-smuggling auditor: searched the import closure for `sorry`, custom
   axioms, conclusion-storing structures and unaudited declarations.

All three returned PASS and found no counterexample. Their substantive
observations are recorded as scope boundaries, not fixes:

- the module has no export bridge, so it is outside the existing audited fact
  graph;
- the result is about one fixed Tate coordinate and one fixed function frame;
- the endpoint, overlap and local-deck hypotheses are local inputs, not
  derived from original etale-theta data;
- the result does not construct an original tempered realization, a primitive
  deck generator, cyclotomic synchronization, Corollary 3.12 or abc.

The pre-existing static route review in `sync-proof-review.md` independently
identified the same proof order, the zero-family obstruction, the same-point
comparison `u` versus `q u`, and the non-constant analytic transition
counterexample. It is not a substitute for the compiled replay or the three
fresh reviews above.

## Boundary

This closes the *analytic synchronization* step for a fixed local q-annular
atlas. It does **not** close the original-source gap. The same-frame
comparison and the local deck equations remain hypotheses. In particular,
different local line-bundle frames can still change the constants by frame
ratios, so no claim is made that arbitrary per-annulus constants can be
identified across unframed sections.
