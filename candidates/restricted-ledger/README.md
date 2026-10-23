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

## Repair increment (2026-10-21)

The old `integer_span_criterion`, `restricted_ledger_criterion`, and the original
equal-valuation two-slot example are retained. Four new principal results are:

1. `integer_combination_criterion`: an affine functional vanishes on a nonempty
   integer-vector set iff its base-point equation and all generator equations
   vanish. `hgen` writes every actual difference as a finite integer combination
   of the fixed generators. `hmem` writes each generator as a finite integer
   combination of actual differences. These two explicit, weight-independent
   certificates express equality of the generated integer submodules; no
   generator is required to be an actual difference.
2. `restricted_ledger_combination_criterion`: applies that equivalence to the
   existing actual `Q_p` weightedLedger and its shift formula. The hypotheses
   explicitly retain a base point in the domain, coordinatewise nonzero points,
   and coordinatewise nonzero scalars. The two generation certificates contain
   only the domain and valuation profiles, never preservation of the ledger.
3. `full_domain_iff`: instantiates the general criterion with unit generators
   and delta tuples on the entire nonzero locus. Preservation is equivalent to
   `forall j, w (sigma j) = w j` and
   `sum j, w (sigma j) * valuation (a j) = 0`. This is the original relabelling
   direction of the scalar budget; under the first conjunct it also equals
   `sum j, w j * valuation (a j)`. No assumption `0 < n` is added.
4. `finite_integer_span_membership_example`: for the one-dimensional finite
   set `{0,2,3}`, base point `0`, and generator `1`, proves nonemptiness, both
   generation certificates, failure of realisation of `1` as an actual
   difference, and the instantiated affine criterion. The reverse certificate
   is `1 = (-1) * (2-0) + 1 * (3-0)`.

`finiteIntegerDomain` and `integerUnitGenerator` are transparent definitions.
`Candidates/Axioms.lean` prints the exact four result types, both definition
bodies, and axiom dependencies of every old and new declaration.

Strict source checking can simultaneously refresh the candidate-local olean:

```
lake env lean --json -DwarningAsError=true Candidates/RestrictedLedger.lean -o .lake/build/lib/lean/Candidates/RestrictedLedger.olean
lake env lean --json -DwarningAsError=true Candidates/Axioms.lean
```

The second command must use the olean produced from the same frozen source by the
first; the repair evidence records both hashes. No dependency upgrade or rebuild
is needed when the existing worktree dependency cache is available. Record the
actual Lean version and githash: a toolchain label alone is not binary identity.

## Span-certificate increment (2026-10-23)

The reviewer gap: `restricted_ledger_criterion` strengthens "the generators generate
the same integer submodule as the actual differences" into "each generator *is* an
actual difference" (`hreal`). Both versions are now present in the same entry file,
and the relation between them is proved:

| version | premise | theorem |
| --- | --- | --- |
| strong (retained candidate) | `hreal : ∀ i, ∃ x ∈ Ω, vprofile x - vprofile x₀ = b i` | `restricted_ledger_criterion` |
| general span certificate | `hspan : ∀ i, MemDiffSpanOn Ω x₀ (b i)` | `restricted_ledger_span_criterion` |

* `MemDiffSpan` (integer vectors) and `MemDiffSpanOn` (points of `Ω`) name the
  `ℤ`-span membership of a generator in the actual differences. Neither body mentions
  a weight vector, a scalar family, the ledger, or preservation.
* `memDiffSpan_of_realised`, `memDiffSpanOn_of_realised`: realisation implies span
  membership (a one-term combination with coefficient `1`).
* `integer_span_criterion_of_combination`, `restricted_ledger_criterion_of_combination`:
  the strong-premise criteria are corollaries of the general ones, so the pair is a
  proved inclusion, not two unrelated assumptions.
* The converse inclusion is false; `finite_integer_span_membership_example` refutes it
  on `{0, 2, 3}` with generator `1 = (-1)·(2-0) + 1·(3-0)`, which is no difference.

### What the full-space specialisation actually gives

`full_domain_specialization` yields only the *necessary* direction
`∀ j, w (σ j) = w j`. `full_domain_iff` yields the full equivalence
`(preservation on the nonzero locus) ↔ (∀ j, w (σ j) = w j) ∧ (Σ_j w (σ j) v(a_j) = 0)`.
Its budget is stated with relabelled weights; it equals the admitted theorem's
`Σ_j w j v(a_j)` only under the first conjunct. Both results instantiate the admitted
`weightedLedger_combined_invariant_iff` through the restricted route, sharing its
base-point, nonzero-point and nonzero-scalar hypotheses; recovering that theorem in
its own form is **not** claimed, and no statement here restores "the whole old
criterion" independently of it.

This remains a mathematical candidate. Actual VS Code observation belongs to the
reviewer, and is not simulated by the CLI. No formal bridge, receipt, or fact-tree
is changed. No actual IUT admissible region or finite certificate for it is
provided; G01/G03 remain open. Preservation on a domain and preservation of the
domain by the transformation remain separate obligations. The empty-domain
example and the old stronger-premise theorem remain available for comparison.