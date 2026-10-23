# W7 — `UnifiedFactorization.lean`: one descent lemma, with W5 and W6 as its two instances

Date: 2026-10-23. Status: **toy province, machine-checked, delivered**. Not a fact-tree entry, not a registry
entry, not an audit of any IUT object. The core GAP of `research/core-backward-2026-10-23/` stays **OPEN**.

## Scope

The task: W5 (`candidates/core-transport/NormalizationAlignment.lean`) proves that for an invariant reading
the orbit average equals the value at the label; W6 (`candidates/core-transport/ReadingFactorization.lean`)
builds `SameObject` as the reflexive–transitive closure of the transport relation and `descendedReading` by
`Quotient.lift`. Both are the same obligation — *the reading lives on the quotient, not on a presentation*
(`research/core-backward-2026-10-23/h1-coricity.md`: `n,◦HT^{D-Θ±ellNF}` is determined only up to
isomorphism, and a poly-isomorphism is an orbit of isomorphisms, txt 2005–2007) — so the deliverable is one
file proving the general statement with the two earlier provinces as instances, plus one concrete failure of
each hypothesis.

Neither earlier file is importable: `lakefile.lean` declares a single library `CoreTransport` whose modules
are those under `CoreTransport/`; both files are top-level modules of the package, are not Lake targets, have
no `olean`, and cannot be imported. What is needed from them is restated in the new file and the module
docstring says so. Two things are deliberately *not* restated: W6's logarithm series (`CoreTransport.localLog`
and its convergence) — here the reading is an arbitrary `α → ℚ_[3]` whose constancy is a hypothesis, not a
theorem — and W5's `orbitAverage` with its division by `Fintype.card`, because only the two-element orbit
occurs and its average is written out.

## What was built

Single new file `candidates/core-transport/UnifiedFactorization.lean`, namespace `UnifiedFactorization`,
import **`CoreLog.QpThree` only**. 85 declarations, 85 dependency-footprint lines.

| item | declaration(s) |
|---|---|
| 1. constancy on the join | `constant_of_join : (∀ a b, R a b → f a = f b) → (∀ a b, S a b → f a = f b) → ∀ a b, Relation.ReflTransGen (fun x y => R x y ∨ S x y) a b → f a = f b`, proved by induction on the closure |
| 2. the joined setoid | `Join`, `join_refl`, `join_symm`, `join_trans`, `join_equivalence`, `joinedSetoid R S hR hS : Setoid α`, `joinedSetoid_rfl` (its relation *is* `Join R S`, definitionally) |
| 3. the descent | `descended R S hR hS f hRc hSc := Quotient.lift f (fun a b hab => constant_of_join hRc hSc a b hab)` |
| 4. the computation rule | `descended_mk : descended R S hR hS f hRc hSc (Quotient.mk (joinedSetoid R S hR hS) a) = f a` (= `rfl`), plus `descended_unique` |
| 5a. instance (a) = W5 | `orbitRel`, `orbitRel_equivalence`, `LabelGroup`, `LabelVector`, `labelVectorMulAction`, `swapLabels`, `labelOrbit`, `sumReading`, `sumReading_of_orbit`, `vecOne`/`vecSwap`/`vecOther`, `orbit_vecOne_vecSwap`, `w5Descended`, `w5Descended_mk`, `w5_average_eq_value`, `classes_distinct` |
| 5b. instance (b) = W6 | `chainInput` (`4, 16, 64`), `chainUnit`, `TransportStep`, `ChainRel`, `relativeInput`, `chainUnit_cocycle`, `relativeInput_eq_of_step`, `relativeInput_eq_of_rel`, `chainRel_equivalence`, `w6Descended`, `w6Descended_mk`, `w6Descended_zero`, `w6Descended_two` |
| 6. anti-degeneracy | `diffReading_not_constant`, `no_factorization_when_S_constancy_fails` (the `hS`-constancy side, `-1` against `1`); `brokenUnit`, `brokenNoStep_02`, `brokenRel_02`, `brokenReading_not_constant`, `no_factorization_on_broken` (the `hR`-constancy side, `4` against `1`) |
| 7. footprint | one `#print` line per declaration, 85 / 85, in `axioms.txt` |

## How each instance reduces to the general theorem

The reduction is not a resemblance: each instance calls `descended` itself, and the two `join_imp_*` lemmas
say that the join in the general statement is the relation that province actually uses.

* **Instance (a).** `w5Descended` is *literally* `descended Eq labelOrbit eq_equivalence
  labelOrbit_equivalence sumReading _ _`, with `hRc` the trivial constancy of a function on equal arguments
  and `hSc = sumReading_of_orbit`, i.e. W5's `Invariant` hypothesis. `join_eq_labelOrbit` shows
  `Join Eq labelOrbit v w → labelOrbit v w`, so the joined relation *is* the orbit relation. On the orbit
  `{vecOne, vecSwap}` the reading is `3` at both points, `w5_average_eq_value` gives
  `(3 + 3) / 2 = 3` — W5's conclusion (average over the orbit = value at the label, its `alignment`) — and
  `descended_mk` supplies it as a statement about classes, not about labels.
* **Instance (b).** `w6Descended` is *literally* `descended (ChainRel chainUnit) Eq
  (chainRel_equivalence chainUnit) eq_equivalence (relativeInput chainUnit) _ _`, with `hRc` proved per step
  from the cocycle law (`relativeInput_eq_of_step` → `relativeInput_eq_of_rel`, W6's `sameObject_reading_eq`)
  and `hSc` trivial. `join_eq_chainRel` shows `Join (ChainRel chainUnit) Eq a b → ChainRel chainUnit a b`, so
  the joined relation *is* W6's `SameObject` and equality contributes nothing. `w6Descended_zero` and
  `w6Descended_two` both compute the descended value as `4`, W6's `descendedReading_const` read at two
  presentations.

## Anti-degeneracy, with the numbers

* **`S`-constancy fails** (instance (a)'s carrier). `diffReading v = v 0 - v 1`; `vecOne = (1, 2)`,
  `vecSwap = (2, 1) = swapLabels • vecOne` (so they are in one orbit), and `diffReading` is `-1` there
  against `1`. `diffReading_not_constant` states the failure of `hSc`; `no_factorization_when_S_constancy_fails`
  proves there is **no** `fBar` on `Quotient (joinedSetoid Eq labelOrbit …)` with `fBar ⟦v⟧ = diffReading v`,
  since `⟦vecOne⟧ = ⟦vecSwap⟧` would force `-1 = 1`.
* **`R`-constancy fails** on the broken chain (`brokenUnit` records `0 → 2` as `4 ^ 3 = 64` instead of
  `4 ^ 2 = 16`). `brokenNoStep_02` shows no one-step relation joins `0` and `2` (`4 * 64 = 256 ≠ 64`),
  `brokenRel_02` shows they are still related in two steps through the untouched elementary transitions, and
  `relativeInput` is `4` at `0`/`1` against `1` at `2`, so `brokenReading_not_constant` refutes `hRc` and
  `no_factorization_on_broken` refutes the existence of a descended function on that quotient.
* In both cases the **equivalence** hypotheses (`labelOrbit_equivalence`, `chainRel_equivalence`) still hold;
  what fails is the constancy of the reading — that is the point of the two examples, and it is stated.

A note on non-degeneracy: unlike W6's chains (whose `SameObject` is total, `sameObject_total`), instance (a)'s
quotient is **not** a subsingleton: `classes_distinct` separates the classes of `vecOne` (sum `3`) and
`vecOther` (sum `6`) using the descended function itself.

## Commands

From `D:\Inter-universal Teichmüller Theory\candidates\core-transport`:

```
lake env lean -DwarningAsError=true UnifiedFactorization.lean
```

Result: **exit 0, stderr 0 bytes, 0 errors, 0 warnings**, one final build (see build history). The file is
not a Lake target, so `lake env lean` re-elaborates it on every run and produces **no** `.olean` (verified:
`UnifiedFactorization.olean` does not exist). Logs: `build.stdout.log` (raw bytes, `cmd.exe` redirection),
`build.stderr.log` (empty), `axioms.txt` (the dependency-footprint output verbatim), `checks.txt` (hashes,
sizes, scans, commands).

## Artifact

| item | value |
|---|---|
| path | `candidates/core-transport/UnifiedFactorization.lean` |
| sha256 | `d822480026ea3121b05753dd9160c01d93b57d3a0df66a601970e1caae4f1af9` |
| bytes / lines / characters | 50694 / 850 / 49991 (LF-only, no CR) |
| namespace | `UnifiedFactorization` |
| imports | `CoreLog.QpThree` (only) |
| declarations | 85 (all 85 audited, one `#print` line each) |
| toolchain | Lean 4.34.0-rc2 (the `candidates/core-transport` package's `lean-toolchain`) |

## Dependency footprint

Three forms occur among the 85 declarations (verbatim in `axioms.txt`):

```
'UnifiedFactorization.Join' does not depend on any axioms                         (14 declarations)
'UnifiedFactorization.orbitRel_equivalence' depends on axioms: [propext]          (1 declaration)
'UnifiedFactorization.constant_of_join' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Union over the file: `{propext, Classical.choice, Quot.sound}` — inside the allowed set. `sorryAx` occurs
0 times in `axioms.txt`. `sorry`, `admit`, `opaque`, `native_decide` occur 0 times in the file; `axiom`
occurs only inside the 85 mandated `#print axioms` lines (0 occurrences outside them, verified by scan).

## Build history (disclosed)

1. **First full build**: 5 errors, all of one kind — `sumReading_of_orbit` and `chainUnit_cocycle` were
   stated with implicit `{a b}` binders, so they could not be passed where `descended` / `relativeInput_eq_of_step`
   expect a function `∀ a b, …`; Lean reported them at 5 call sites and generated `sorryAx` for the affected
   declarations.
2. **Repair round 1** (the only repair round): both lemmas restated in `∀`-form (matching the shape of the
   general statement's hypotheses) — no proof changed, no goal was ever left open, no literal `sorry` was
   written at any point.
3. **Final build**: exit 0, stderr 0 bytes, 0 warnings, `sorryAx` everywhere gone.

Earlier, small probe files (`ProbeW7*.lean`) were compiled in the same directory to pin down three API
details before writing the deliverable (the `MulAction` instance for `Equiv.Perm` on a function space does not
exist in Mathlib; type aliases must be `abbrev` for instance search; `Fin` numerals from `fin_cases` are not
syntactically `OfNat`). They have been deleted; only the deliverable remains.

## Non-claims

1. **What the unification does not say about the IUT object**: it identifies the *shape* of two obligations —
   constancy on a generated relation, hence a function on its quotient — and does not say that the IUT object
   carries two such relations, nor that any reading of the real object is presentation-independent.
2. No procession, capsule, theta value, Θ-link, `F_l^⋆`, `|F_l|`, `⟨F_l^⋆⟩`, F-prime-strip, Frobenioid,
   log-volume, log-shell, Hodge theater, coricity, poly-isomorphism, `Ism`, `Ind1`/`Ind2`/`Ind3`, `M`, `N_E`,
   packet normalization or `det^{⊗M}` occurs in the file. `LabelGroup` is `Equiv.Perm (Fin 2)`; `Fin 3` is a
   set of indices, not the set of places of a number field; the transports are multiplication by powers of
   `4` on `ℚ_[3]`; `TransportStep` is not an `Ism`.
3. `ℚ_[3]` is used only as a commutative field in which the two sides of each anti-degeneracy can be
   *computed*: no norm, no valuation, no logarithm.
4. The unification is formal. It does not upgrade W5's averaging into a theorem about non-constant readings,
   and it does not give W6 a non-trivial quotient on its own carrier (that is supplied here only by instance
   (a), whose carrier is a function space, not a chain).
5. Not evidence for or against any IUT claim. The core GAP stays OPEN.
