# Rank-0 / rank-1 targets, run through CDS-A (round 9)

Two obligations from `research/round3-realization-obligations.md` were attacked in parallel,
each in its own git worktree (branch `explore/narc`, `explore/ind`), and then all claims were
re-derived by independent verification nodes under the CDS-A composition
(`cdsa/specs/next-targets.json`, 4 nodes, digest `806c34486a0f1d4e`).

Acknowledgement of what this document is: a **process-integrity** report. Gates going green
means the two candidates compile with zero diagnostics, carry no forbidden terms, keep their
axioms inside `{propext, Classical.choice, Quot.sound}`, and do not claim more in prose than
the artifacts show. It is **not** mathematical admission of anything, and it says nothing
about the Θ-link, `Ism`, Cor 3.12 or `abc`.

## Rank 0 — `NonarchimedeanRing ℚ_[p]` is now closed

Independent starting point (mine, before seeing any worker output): with `import Mathlib`,
`#synth NonarchimedeanRing ℚ_[p]` **fails**. The class is
`Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean:49`; the only ready-made instance route is
`WithIdeal R` (`AdicTopology.lean:246`), whose topology *comes from* a preferred ideal, so it
never unifies with `Padic`'s norm topology. The ledger's reading was correct.

`candidates/nonarchimedean-ring` supplies the missing instance from
`Metric.mem_nhds_iff` plus `Padic.nonarchimedean` (`PadicNumbers.lean:834`): every
neighbourhood of `0` contains `Metric.ball 0 ((p:ℝ)⁻¹ ^ n)` as an `OpenAddSubgroup`.

What it buys, verified rather than asserted: four lemmas of
`InfiniteSum/Nonarchimedean.lean` (`:104`, `:126`, `:135`, `:139`) were **unstatable** at
`R = ℚ_[p]` and are now statable, e.g.

```
theorem tsum_mul_tsum (f g : ℕ → ℚ_[p]) (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) * (∑' j, g j) = ∑' i : ℕ × ℕ, f i.1 * g i.2
```

The general lemmas do not substitute: `HasSum.mul` (`InfiniteSum/Ring.lean:178`) and
`Summable.tsum_mul_tsum` (`:186`) require `Summable (f i * g j)` as an *extra* hypothesis, and
`tsum_mul_tsum_of_summable_norm` (`Analysis/Normed/Ring/InfiniteSum.lean:70`) needs
norm-summability, which is strictly stronger in a nonarchimedean field.

**What it does not buy.** The p-adic `log`/`exp` gap (`RESULTS.md:65`) is untouched; only the
convergence kit moves. And the two "non-vacuity consequences" my own task brief asked for are
**not consequences of this class**: `‖x+y‖ ≤ max ‖x‖ ‖y‖` is `Padic.nonarchimedean` and
`IsUltrametricDist ℚ_[p]` is a pre-existing instance, both independent of `NonarchimedeanRing`,
which constrains the topology and not the norm. The candidate states this instead of hiding it,
and uses `exists_openAddSubgroup_subset_closedBall` as the real witness that the instance
carries content. My brief was wrong here; the artifact says so.

## Rank 1 — the Ind1–Ind3 family, relation-valued

`candidates/ind-relations` models `Tuple p := Fin 4 → ℚ_[p]` with `Allowed12` defined as a
**relation** (`∃` relabelling generator, `∃` slotwise scalars, equation), never as a group
action and never with its generators identified as elements of one isomorphism monoid (F-01).

Proved: `allowed12_subset` (inclusion in the ambient `A(k)`-style family),
`allowed12_strict` (with the exactness witness `e 3 ↦ e 2`: `Γ12` fixes slot `3` and every
scalar is `1` there, so `e 3` cannot leave itself), `compositionClosed_of_closed` (conditional),
`gamma12_trans_mem` (the `Γ12` hypothesis discharged — it *is* a subgroup),
`not_scaling_family_closed`, and `not_compositionClosed` (the raw family really is not closed).

The projection equation, as literally proved:

```
move_projection :          move σ a x (σ j) = (a j : ℚ_[p]) * x j
move_projection_source :   move σ (pull σ a) x (σ j) = (a (σ j) : ℚ_[p]) * x j
```

### Six corrections to the ledger's wording

These came out of the formalization, not out of review, and the first one matters.

1. **F1 — the ledger's literal projection formula is false.** For a single *target-indexed*
   scalar family the identity `… (σ j) = a (σ j) * x j` fails; the true form is `a j * x j`. The
   ledger's literal shape is recovered only after transporting the scalars to the source slots
   (`pull σ a`). Any argument that quotes the literal form is quoting a false statement.
2. **F2 — the closure hypothesis was mis-stated.** It is not "`S` closed under pointwise
   product" but closure under `pull σ b * a`. `Γ12` can be a genuine subgroup while closure
   still fails, so a subgroup check does not establish closure.
3. **F3 — closure genuinely fails for the raw family.** Therefore any future closure claim must
   enlarge `S` *and* re-prove strictness against `A(k)`; enlarging `S` eats the strictness
   witness unless the exactness argument is redone.
4. **F4 — strictness is an exactness property**, not a counting property: what makes `e 3`
   immovable is a slot value no generator can touch. Counting generators would not survive a
   harmless enlargement.
5. **F5 — the composition order is convention-dependent** (`σ.trans ρ` under
   `relabel σ x i = x (σ.symm i)`); the ledger's prose leaves the order ambiguous.
6. **F6 — environment**: `candidates/orbit-quotient` is absent on this branch (structure taken
   from `pilot-shadow`); Lake needs `require iut_bridge from "../../bridge"`; `Tuple` must
   carry the `Fact p.Prime` parameter.

## The gates, and what they caught

`cdsa/runs/next-02` (green) and `cdsa/runs/next-01-red` (kept deliberately) are the receipts.

The first pass **failed** and the failure was worth keeping: `N3-crosscheck` came back red
because its own claim text contained the token `Ism`, which its own `forbidden_in_claim` list
forbids. The contract was over-broad, not the candidate. A second defect surfaced on the same
pass: the claim-consistency audit rejected the rank-1 README for having no `VERDICT:` line —
the line existed, wrapped in backticks — and for `Cor 3.12` with a leading "**no**" that my
phrase list did not recognise as a negation. The audit now checks for a *negation token near the
mention* instead of a fixed phrase list, which is the actual grammar of hedging.

While pointing the checker at real candidates, it also lost wrapped axiom lists (they span two
lines), never matched qualified report names against unqualified declarations, and needed
`lake build` before the companion probe could import the module. All four defects are recorded
in `cdsa/checks/README.md`; the calibration pair (PASS on the existing pilot candidate, FAIL on
a planted `sorry`) is re-run after every fix.

## Residual state

- Rank 0: **closed** as a Lean obligation. The p-adic log/exp gap remains open.
- Rank 1: the *shape* is now formalized and its safety property proved; the *content* of the
  real Ind1–Ind3 procession is absent, and the ledger's projection formula needs correcting in
  `research/round3-realization-obligations.md` (RI-01/RI-04/RI-05 wording).
- Next cheapest targets by the same pattern: rank 2 (a `SeededFamily` instantiation for a
  possible image) and the log-shell half of the log/Kummer line, both still blocked on the same
  missing input, not on Lean effort.
