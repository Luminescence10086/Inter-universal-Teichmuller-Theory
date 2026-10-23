# W6 鈥?`ReadingFactorization.lean`: the reading descends to the quotient

Date: 2026-10-23. Status: **toy province, machine-checked, delivered**. Not a fact-tree entry, not a registry
entry, not an audit of any IUT object.

## Scope

W4 (`candidates/core-transport/TransitionCompatibility.lean`) proved the reading is **constant on a compatible
chain** (`reading_compatible`). W6 takes the next step: the transition data must induce an **equivalence
relation** on the presentations, and the reading must be a **function on its quotient** 鈥?a `Quotient.lift` 鈥?whose computation rule recovers the original values.

Single new file `candidates/core-transport/ReadingFactorization.lean`, namespace `ReadingFactorization`,
imports `CoreTransport.Basic` and `CoreLog.QpThree` only. Nothing else was modified: no existing file, no
`tools/`, no fact-tree, no registry, no other candidate.

## What was built

* **Restated locally (task item 1)** 鈥?`algorithmRun`, `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`,
  `hasSum_logTerm_localLog` (quoted from `CoreLog.principal_unit_log_hasSum`), plus W4's chain structure,
  reading, `IsCompatible`, `input_transport`, `reading_eq_base`, `reading_compatible`, the two concrete chains
  and the `localLog 4 鈮?0` separation with its remainder estimates. `TransitionCompatibility.lean` and the other
  W-files are **not Lake targets** (`lakefile.lean`: `lean_lib CoreTransport`, modules only under
  `CoreTransport/`), hence no `olean`, hence not importable; the module docstring says so. The restatements
  carry no new mathematics.
* **`Chain k` / `IsCompatible`** (items 2): transition-carried chain with `unit`, `step_eq`, `stepInv`,
  `unit_refl`, `step_input`; the cocycle law is a hypothesis, not a field.
* **`SameObject`** (item 3): `SameObjectStep c a b` says the recorded transition between `a` and `b` (whichever
  orientation is defined) actually transports the presentation 鈥?`input a * unit a b h = input b`;
  `SameObject c i j` is its reflexive鈥搕ransitive closure. **Built from the transition data only; it never
  mentions the reading**, which is what makes item 6 possible at all.
* **Equivalence relation** (item 4): `sameObject_refl`/`_step_refl`, `sameObject_symm` (needs a locally proved
  `reflTransGen_symm`; Mathlib's `Relation.ReflTransGen` has no symmetry lemma), `sameObject_trans`,
  `sameObject_equivalence`, `sameObjectSetoid`, `sameObjectSetoid_rfl` (the setoid's relation *is* `SameObject`,
  by `rfl`).
* **The quotient and the lift** (items 4鈥?): `descendedReading c hc : Quotient (sameObjectSetoid c) 鈫?鈩歘[3] :=
  Quotient.lift (reading c) _`, with obligation `sameObject_reading_eq`; `descendedReading_mk : descendedReading
  c hc 鉄鉄?= reading c i`; `descendedReading_const`; `descendedReading_unique` (the descent is the only such
  function 鈥?no chain-level analogue).
* **Anti-degeneracy** (item 6), with explicit numbers: `chainCompat` (comparison `0 鈫?2` is `16`, `4 * 16 = 64`
  = input 2, so `0 ~ 2` in **one** step) against `chainBroken` (comparison `0 鈫?2` is `64`, `4 * 64 = 256 鈮?64`).
  On `chainBroken`: `chainBroken_no_direct_edge` (the one-step relation is *strictly smaller*),
  `chainBroken_sameObject_one_two` / `chainBroken_sameObject` (still related 鈥?one step via the correct
  elementary transition `16 * 4 = 64`, and `0 ~ 2` in two steps), `chainBroken_readings_one_two_differ`
  (`localLog 4` vs `0`), `constancy_not_universal_on_broken`, and `no_factorization_on_broken`: **no** function
  on the quotient computes the readings of `chainBroken`.

### Transitive closure: needed, and why it is not a dodge

The structure records a unit only for ordered pairs `i 鈮?j` and imposes **no** relation between `unit a b` and
`unit b a`, so the one-step relation is not transitively closed in mixed orientations as it stands; the
quotient of a non-transitive relation is its closure. What is then proved is that on a compatible chain the
closure is **redundant**: `sameObjectStep_direct` gives every pair a **single** edge (via
`sameObjectStep_of_compatible`, the cocycle law), so `SameObject` is the one-step relation there.

### Which item-6 fact is proved, and the honest limitation

Both alternatives are proved, and neither is impossible here 鈥?because `SameObject` is built from transition
data and never from the reading, it can relate two indices whose readings differ. (Had it been defined as
equality of `relativeInput`, constancy would hold by `congrArg` and the anti-degeneracy would be vacuous.)

Limitation, stated not hidden: `step_input` is a **field**, so `SameObject` is total on *every* chain
(`sameObject_total`) and the quotient is a subsingleton (`sameObject_quotient_subsingleton`) for both chains.
The quotient's *shape* therefore cannot distinguish them; what distinguishes them is whether the reading is
constant on it, i.e. whether the descent exists at all. A nontrivial quotient would require the elementary
transports to be fallible data, which would make the reading's definition moot 鈥?a limit of the toy, recorded
in the module docstring.

## Commands

From `D:\Inter-universal Teichm眉ller Theory\candidates\core-transport`:

```
lake env lean -DwarningAsError=true ReadingFactorization.lean
```

Result: **exit 0, stderr 0 bytes** (28.4 s), one build, no goal left open, no proof written around.
Logs: `build.stdout.log` (16772 bytes), `build.stderr.log` (0 bytes), `axioms.txt` (83 lines), `checks.txt`.

## Artifact

| item | value |
|---|---|
| path | `candidates/core-transport/ReadingFactorization.lean` |
| sha256 | `6a756a88d57eed9892e749eb0c8abea75c1aa289bd0556f44c3e9f8e5fb2716d` |
| bytes / lines | 55759 / 881 |
| namespace | `ReadingFactorization` |
| imports | `CoreTransport.Basic`, `CoreLog.QpThree` |
| declarations audited | 83 of 83 (every named declaration has one `#print axioms` line) |

## Dependency footprint

`#print axioms` for all 83 declarations (verbatim in `axioms.txt`). Distinct forms:

```
'ReadingFactorization.algorithmRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReadingFactorization.base' depends on axioms: [propext]
'ReadingFactorization.i0' does not depend on any axioms
```

Union over the file: `{propext, Classical.choice, Quot.sound}`. Forbidden substrings (`sorry`, `admit`,
`opaque`, `native_decide`, `sorryAx`) do not occur; `axiom` occurs only inside the 83 mandated `#print axioms`
lines.

## Non-claims

The file says **nothing** about IUT's localisation data: not about `鈯糵Q鈧乣, `鈯糵Q鈧俙, the formal quotient
`鈯糵Q鈧?modulo 鈯糵Q鈧乣, log-volumes, log-shells, 螛-links, `Ism`, Corollary 3.12, Hodge theaters, coricity,
poly-isomorphisms, Galois actions, prime-strips or Frobenioids. `Fin k` is a set of indices, not the places of
a number field; the transitions are multiplication by powers of `4` on `鈩歘[3]`, not localisation morphisms; the
logarithm series is not the 畏-algorithm; `SameObject` is not an `Ism`. Nothing here shows that any reading of
the real object is presentation-independent, and nothing here is evidence for or against any IUT claim. What is
shown is that the invariance obligation of 搂缁撹涓€鈥?has the shape of a *descent*: transition data induce an
equivalence relation, the reading factors through the quotient, and the factorisation can fail 鈥?with explicit
numbers 鈥?when the cocycle law is dropped.

