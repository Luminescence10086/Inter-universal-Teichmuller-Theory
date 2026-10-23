# W4 — `TransitionCompatibility.lean`: compatible transitions replace W2's toy equality

Date: 2026-10-23. Status: **toy province, machine-checked, delivered**. Not a fact-tree entry, not a
registry entry, not an audit of any IUT object.

## Scope

W2 (`candidates/core-transport/CollectionProvenance.lean`) attached execution provenance to a collection of
local pieces, but related the global reading to the local ones by one equation, `globalValue = localValue v`
— a *toy equality*, i.e. agreement of values because the values are literally the same. Actual local-global
data instead relates pieces by **transitions** (isomorphisms between presentations of one object), and a
reading survives the passage to the object only when those transitions are **compatible**. This file
replaces the toy equality with that structure and proves both directions of the contrast:

* `reading_compatible` — a chain whose transitions satisfy the cocycle law has one reading across all
  presentations (the sharp form is `reading_eq_base`: every reading equals the base reading);
* `chainBroken_readings_differ` — a concrete chain with explicit numbers whose transitions fail the law
  and whose readings differ (`localLog 4` versus `0`).

Motivation recorded in `research/core-backward-2026-10-23/h1-decision.md`, §结论一′: `(n,◦)` is determined
only **up to isomorphism**, so a reading on a chosen presentation is a reading of the presentation unless
invariance is proved. That is the obligation this file formalises the shape of, on one concrete case.

## What was built

Single new file `candidates/core-transport/TransitionCompatibility.lean`, namespace
`TransitionCompatibility`, imports `CoreTransport.Basic` and `CoreLog.QpThree` only.

* **Restated locally** (item 1 of the task): `algorithmRun`, `localLog_eq_padicLog`,
  `hasSum_logTerm_localLog` (quoted from `CoreLog.principal_unit_log_hasSum`), plus
  `algorithmRun_eq_partialSums`. `CollectionProvenance.lean`, `ExecutionProvenance.lean` and
  `ReadingInvariance.lean` are top-level modules of the package and **not Lake targets** (`lakefile.lean`
  declares only `lean_lib CoreTransport`), so no `olean` exists and they cannot be imported. The
  restatements carry no new mathematics and the module docstring says so.
* **`PresentationChain k`** (`k ≥ 1` via `NeZero k`, base index `⟨0, _⟩`): `input`, `mem`, transitions
  `step : ∀ i j, i.val ≤ j.val → ℚ_[3] → ℚ_[3]` acting as multiplication by a principal unit `unit`
  (`step_eq`), with inverse `stepInv` (`stepInv_step`), identity `unit_refl`, and the transport field
  `step_input` for the elementary steps `i → i+1`.
* **`IsCompatible`** — the cocycle law `unit i l = unit i j * unit j l` for `i ≤ j ≤ l`, a hypothesis.
* **The reading** — `localLog` of the presentation transported back to the base frame
  (`relativeInput`, `reading`), a genuine limit (`reading_hasSum`, `reading_is_limit_of_algorithm`,
  domain membership `relativeInput_mem`); it is *not* defined as `localLog` of a fixed point.
* **`reading_compatible`** and the sharpening `reading_eq_base`, via `input_transport` (induction; the
  cocycle is consumed once per step).
* **Anti-degeneracy** — `chainCompat` (compatible; readings all `localLog 4`) versus `chainBroken`
  (incompatible; readings `localLog 4` at `0` and `0` at `2`), differing **only** in the recorded
  comparison transition `0 → 2` (`16` versus `64`), by
  `difference_lies_in_the_direct_transition`.

A design point is stated in the module docstring rather than hidden: on the principal units of `ℚ_[3]`
multiplication is sharply transitive and the logarithm injective, so a model in which *every* transition
was required to transport the presentation would determine the comparison units from the inputs, make the
cocycle law automatic, and force equal readings **by construction** — item 4 would then be impossible and
no theorem would remain. Hence the model records elementary transports (a field) and comparison
transitions (data) separately, and the cocycle law is a real hypothesis whose failure is exhibited.

## Commands

From `D:\Inter-universal Teichmüller Theory\candidates\core-transport`:

```
lake env lean -DwarningAsError=true TransitionCompatibility.lean
```

Result: **exit 0, stderr 0 bytes**, one build, no goal left open, no proof written around. Details, logs
and scans: `checks.txt`, `build.log`, `build.stdout.log`, `build.stderr.log`, `axioms.txt`.

## Artifact

| item | value |
|---|---|
| path | `candidates/core-transport/TransitionCompatibility.lean` |
| sha256 | `3fb9783ac84702383fe2369e000dd815fb3087fe584c3e6e3cfa9f25b1184cc4` |
| bytes / lines | 39140 / 619 |
| namespace | `TransitionCompatibility` |
| imports | `CoreTransport.Basic`, `CoreLog.QpThree` |

## Dependency footprint

`#print` lines for every one of the 50 declarations (verbatim in `axioms.txt`). Distinct forms:

```
'TransitionCompatibility.algorithmRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TransitionCompatibility.base' depends on axioms: [propext]
'TransitionCompatibility.i0' does not depend on any axioms
```

Union over the file: `{propext, Classical.choice, Quot.sound}`. Forbidden substrings
(`sorry`, `admit`, `opaque`, `native_decide`) do not occur; `axiom` occurs only inside the mandated
`#print axioms` lines.

## Non-claims

The file says **nothing** about IUT's localisation data: not about `⊼fQ₁`, `⊼fQ₂`, the formal quotient
`⊼fQ₂ modulo ⊼fQ₁` of §结论二, log-volumes, log-shells, Θ-links, `Ism`, Corollary 3.12, Hodge theaters,
coricity, poly-isomorphisms, Galois actions, prime-strips or Frobenioids. `Fin k` is a set of indices, not
the places of a number field; the transitions are multiplication by powers of `4` on `ℚ_[3]`, not
localisation morphisms; the logarithm series is not the η-algorithm. Nothing here shows that a reading of
the real object is presentation-independent, and nothing here is evidence for or against any IUT claim.
What is shown is that the obligation of §结论一′ has a formally checkable shape with a real hypothesis:
drop compatibility and the readings separate, at explicit numbers.
