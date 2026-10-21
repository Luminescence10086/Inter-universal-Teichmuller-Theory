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
| `Candidates/OrbitQuotient.lean` | the single concentrated entry file (5 main theorems + auxiliary lemmas, all exported) |
| `Candidates/Axioms.lean` | axiom export for the main theorems |
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
