# `candidates/orbit-quotient` — M2 candidate project

Isolated candidate project for task **M2** of `handoffs/next-round`
(“有限局部商环中的轨道矩形包络与精确计数”).  Base commit
`484127185878e65b10795d20568bd3714eebc798`, branch `task/m2`.

Nothing here is admitted to any fact tree; `mathematical_goal_status` stays
`UNPROVED_CANDIDATE` until a reviewer replays the frozen commands in an actual
VS Code session.

## Toolchain and dependency lock

* `lean-toolchain` — `leanprover/lean4:v4.34.0-rc2`, the same toolchain as the
  worktree's `local-field` project.
* `lakefile.toml` — library `Candidates`, requiring Mathlib from the external
  absolute path `C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib`.
* `lake-manifest.json` — copy of `local-field/lake-manifest.json` with the
  project name changed to `orbit_quotient_candidates`; every package `dir` is
  the external absolute path, so no network access is needed.
* Builds are confined to this directory's own `.lake` cache; the main
  workspace's `.lake` is never written.

## Files

| file | role |
| --- | --- |
| `Candidates/OrbitQuotient.lean` | the concentrated original entry plus 3 repair theorems and auxiliary lemmas |
| `Candidates/Axioms.lean` | complete declaration type and axiom export |
| `Candidates.lean` | library root, re-exports the entry file only |

## Frozen verification commands

From this directory (`candidates/orbit-quotient`):

```text
lake build
lake env lean --json -DwarningAsError=true Candidates/OrbitQuotient.lean
lake env lean --json Candidates/Axioms.lean
```

`lake build` is a prerequisite of the axiom command only: it creates
`.lake/build/lib/lean/Candidates/OrbitQuotient.olean`, which
`Candidates/Axioms.lean` imports.  The entry-file command does not need it.

## Scope

Finite counting here is not a log-volume, and the global error budget / real
seed identities remain independent obligations.  See `SUMMARY.md` in the
external delivery package.

## Incremental rectangular-product repair (2026-10-21)

Repair base: `e9eff929ff63f5faf993abc08f3b7ef84de3b9ee`. Three new main theorems
close the former bounded-threshold-only interface: `coordinateProductHull_minimal`,
`coordinateProductHull_orbitUnion`, and `hull_minimal_coordinateProduct`.
The product hull is defined as `Set.pi Set.univ (fun j => (fun x => x j) '' U)`.
Its equality with `Box (hullThresh Γ hΓ k)` and minimality hold for every nonempty
finite family `Γ`; these set-theoretic results do not require primality, bounded
thresholds, identity membership, or a group structure. Counting results retain
all their original assumptions.

Direction is explicit: `permAct γ x = x ∘ γ`, while the unchanged `orbitUnion`
uses inverse images. The new auxiliary lemma `orbitUnion_eq_inverse_images`
proves that it equals the union of images under `permAct γ.symm`. This is not an
assertion that a general finite family equals its inverse family. Consequently
the existing hull threshold `k (γ.symm j)` is correct for the retained definition.

The entry, original cardinality/budget proofs and 2/3/4 example are checked
once per frozen replay. To avoid triggering dependency builds, the replay emits
the candidate olean directly using the existing locked dependency caches:

```text
lake env lean --json -DwarningAsError=true -o .lake/build/lib/lean/Candidates/OrbitQuotient.olean -i .lake/build/lib/lean/Candidates/OrbitQuotient.ilean Candidates/OrbitQuotient.lean
lake env lean --json -DwarningAsError=true Candidates/Axioms.lean
```

The second command exports every declaration's exact type and axiom dependencies,
plus the original and added definition bodies. Evidence is stored outside the
candidate source in the main workspace's `reviews/repair-round/m2/`. Actual VS Code
observation is a separate reviewer obligation; this remains candidate-only.

## Round-2 increment (2026-10-23): equivalent form of the task definition

Repair base: `2a13a5bca589bd1100c48282ca30cf0e1e55acce`. Two further main
theorems make the reviewer's second alternative (“equivalent theorem for the task
definition of `H`”) explicit; the earlier repair already discharged the first
alternative (minimality against arbitrary products).

* `hull_least_coordinateProduct` — `U ⊆ Set.pi Set.univ S ↔ H ⊆ Set.pi Set.univ S`
  for every family `S` of arbitrary coordinate subsets (unconstrained coordinates
  are the case `S j = Set.univ`). The two sides are the two halves of “`H` is the
  smallest product containing `U`”: `←` says `H` contains `U`, `→` says every
  product containing `U` contains `H`. No bounded-threshold, primality or group
  hypothesis is used.
* `hull_minimal_from_products` — the older bounded-threshold statement
  (`hull_minimal`, with `k' ≤ N` and `p` prime) is derived from the
  arbitrary-product statement, so the new interface contains the old one; the
  derivation no longer needs primality or `k' ≤ N`.

Direction (`σ`/`σ⁻¹`) is unchanged and stays explicit: `permAct γ x = x ∘ γ`,
`orbitUnion` uses inverse images, `orbitUnion_eq_inverse_images` proves
`U = ⋃ γ ∈ Γ, permAct γ.symm '' B k`, and `mem_permAct_box` proves
`permAct γ x ∈ B k ↔ x ∈ B (j ↦ k (γ.symm j))`. Cardinality
(`box_cardinality`: `|B k| = p ^ ∑ j, (N - k j)`), the integer enlargement budget
(`enlargement_budget`, `enlargement_budget_hull`) and the `2/3/4` example
(`two_three_four`) are unchanged.

Frozen replay commands are the same three as above (or the two `-o`-style commands
in the previous section, which avoid dependency builds).

