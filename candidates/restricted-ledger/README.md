# Candidate project: restricted-ledger (task M1)

Isolated candidate Lean project for task M1 of `handoffs/next-round/contracts.json`.
It reuses the admitted bridge library of this worktree (no redefinition of the
ledger) and keeps its own build cache. Nothing here is admitted to any fact-tree,
no receipt is touched, and no IUT/abc claim is made.

## Contents

| path | role |
| --- | --- |
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` (same as the bridge) |
| `lakefile.toml` | package `candidates`, library `Candidates`, requires `iut_bridge` at `../../bridge` |
| `lake-manifest.json` | pinned dependency graph, copied from `bridge/lake-manifest.json` with `dir` entries rewritten relative to this directory (external Mathlib checkout kept absolute) |
| `Candidates.lean` | library root |
| `Candidates/RestrictedLedger.lean` | the single central entry file (all mathematics) |
| `Candidates/Axioms.lean` | non-mathematical export file: `#print axioms` for every declaration |

## Build

Dependencies (`local_field_audit`, `iut_bridge`, Mathlib) must be built once; their
oleans land in the worktree's gitignored `.lake` directories, never in another
workspace:

```
cd candidates/restricted-ledger
lake build
```

## Frozen verification commands (run from `candidates/restricted-ledger`)

```
lake env lean --json -DwarningAsError=true Candidates/RestrictedLedger.lean
lake env lean --json Candidates/Axioms.lean
```

The first must exit 0 with empty output. The second must report, for every
declaration, an axiom set contained in `{propext, Classical.choice, Quot.sound}`.

Note that the second command *imports* `Candidates.RestrictedLedger`, so it requires
the olean produced by the `lake build` above; the first command elaborates the source
directly and needs only the dependency oleans.
