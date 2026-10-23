# W7 — gate record and path record

Deliverable: `candidates/core-transport/UnifiedFactorization.lean`
sha256 `d822480026ea3121b05753dd9160c01d93b57d3a0df66a601970e1caae4f1af9`, 850 lines,
85 declarations, 85/85 axiom reports.

**Path record for this batch**: `research/core-backward-2026-10-23/PATH.md` (commit `37ca819`) — the
document that states, in one place, the shape of the line being walked, every step already taken with its
artifact and commit, W7 as the step in flight, the next three items in order, and the three prohibitions
each step is checked against.

## What W7 unifies

W5 showed "invariant reading ⇒ orbit average = value at the label"; W6 showed "reading descends to the
quotient of a transport-generated relation". W7 states the common shape once:

```
theorem constant_of_join (hR : ∀ a b, R a b → f a = f b) (hS : ∀ a b, S a b → f a = f b) :
    ∀ a b, Relation.ReflTransGen (fun x y => R x y ∨ S x y) a b → f a = f b
```

and then descends: `joinedSetoid` makes the join an equivalence relation, `descended` is
`Quotient.lift f (constant_of_join …)`, and

```
theorem descended_mk … : descended R S hR hS f hRc hSc (Quotient.mk (joinedSetoid R S hR hS) a) = f a
```

Both earlier results are recovered as instances that call `descended` itself: `join_eq_labelOrbit` shows
`Join Eq labelOrbit` *is* the orbit relation (W5), and `join_eq_chainRel` shows `Join ChainRel Eq` *is*
W6's `SameObject`.

## Gates

- CLI: exit 0, stderr 0 bytes; independent strict re-check **PASS** — 85 declarations, 0 errors,
  0 warnings, 85 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- Editor: trusted workspace, Lean 4 active — **0 errors, 0 warnings**, information entries present.
  Capture: `editor/vscode-observation-tree-2.txt`.
- Infoview: not attempted (the batch's three gates are CLI, axiom whitelist, editor zero diagnostics).

## Anti-degeneracy, both sides

- `S`-side: `diffReading v = v 0 - v 1` is `-1` at `vecOne = (1,2)` and `+1` at
  `vecSwap = (2,1) = swapLabels • vecOne` — the same orbit, so the `S`-constancy hypothesis fails and
  `no_factorization_when_S_constancy_fails` proves no function on the joined quotient computes it.
- `R`-side: `brokenUnit` records `0 → 2` as `4^3 = 64` (`4*64 = 256 ≠ 64`, no direct edge) while `0` and
  `2` remain related in two steps with readings `4` and `1` ⇒ `no_factorization_on_broken`.

## What this does not say

It unifies only the *shape* of the W5/W6 obligation: constancy on a generated relation gives a function on
its quotient, and failure of constancy gives no such function. It does not assert that the IUT object
carries two such relations, nor that any reading of the real object is presentation-independent. Nothing
here touches Θ-links, `Ism`, log-volumes or Cor 3.12. Core GAP stays OPEN, `fact_tree_admitted` is false.
