# research/: evidence directories are now tracked

## What was wrong

212 files under `research/` and 203 `.md` files across the repository were
untracked, including five directories that delegated tasks and the W-series
lean on directly:

| directory | files | tracked before |
|---|---|---|
| `research/core-germ-2026-10-24` | 15 | 0 |
| `research/core-kummer-2026-10-24` | 19 | 0 |
| `research/core-boundary-2026-10-24` | 25 | 0 |
| `research/core-comparison-2026-10-24` | 11 | 0 |
| `research/core-projective-2026-10-24` | 9 | 0 |

None of them was blocked by `.gitignore`; they had simply never been added.
Anyone cloning the repository therefore could not see the evidence behind
T008's arrow table or T097's quantifier ledger, because that evidence did not
exist outside one working tree.

`.gitignore` does exclude `reviews/` on purpose (the reviewer workspace), and
that exclusion stands. It does not exclude `research/`, and never did.

## One nested repository had to be moved out

`research/core-kummer-2026-10-24/continuous-kummer-pin` was a full git checkout
with its own `.git`. Adding it would have recorded a gitlink instead of the
files, so a clone would have received an empty directory. It has no remote
configured, so it cannot be added as a submodule either.

It was moved to `.wt/external-pin` and is **not** part of this commit. Its
provenance is consequently unrecorded: the tree is a local copy of an upstream
that names itself in `lake-manifest.json` (mathlib `v4.32.0`, rev
`81a5d257...`), but nothing pins where the outer project itself came from. Until
that is established, treat the copy as `LOCAL_ONLY_EVIDENCE`.

## What this commit does not do

- It does not add the remaining untracked material: the GAP documents, the six
  `fact-tree/*-2026-10-24.json` nodes, the `handoffs/` packages, `model-tools/`,
  and the `research/` files outside the five directories above. Those are still
  untracked and still invisible to anyone who clones.
- It does not claim any of this evidence is correct. Tracking a file says where
  it is, not what it proves.
