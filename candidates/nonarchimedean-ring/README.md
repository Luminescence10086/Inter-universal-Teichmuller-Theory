# Candidate: `NonarchimedeanRing ℚ_[p]`

Worktree `D:\iut-wt\x-narc`, branch `explore/narc`. Nothing outside
`candidates/nonarchimedean-ring/` was modified; `tools/` was not touched.

## Verdict

```
VERDICT: INSTANCE_PROVED_UNBLOCKS
```

The instance had to be **built** (it is not free in Mathlib), and it demonstrably unblocks the
nonarchimedean infinite-sum family in `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean`
— including `HasSum.mul_of_nonarchimedean`, which is precisely what the ledger recorded as
blocked. It does **not** unblock `p`-adic `log`/`exp`, and it says nothing about IUT.

## 1. Exact class name (verified, not guessed)

```
Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean:49
class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] : Prop
  extends IsTopologicalRing R where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U
```

Verified by:

```
Select-String -Path (Get-ChildItem Mathlib -Recurse -Filter *.lean).FullName -Pattern "class NonarchimedeanRing"
  -> Mathlib\Topology\Algebra\Nonarchimedean\Basic.lean  49
```

Neighbour names in the same file: `NonarchimedeanAddGroup` (:37), `NonarchimedeanGroup` (:43),
`NonarchimedeanRing.to_nonarchimedeanAddGroup` (:55). It is a `Prop`-valued class, so it cannot be
inhabited "bogusly": the obligation is real mathematics (open additive subgroups inside every
neighbourhood of `0`), and `sorry/admit/axiom/opaque/native_decide` cannot fake it.

## 2. The gap, reproduced before the fix

`Probe.lean` (scratch, deleted before commit) imported only
`Mathlib.NumberTheory.Padics.PadicNumbers`,
`Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology` and
`Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`, then asserted:

```
lake env lean Probe.lean
Probe.lean:19:38: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NonarchimedeanRing ℚ_[p]
Probe.lean:24:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NonarchimedeanRing ℚ_[p]
```

The second error is `HasSum.mul_of_nonarchimedean` at `R = ℚ_[p]` — the ledger's claim is exactly
right. Also observed: `#synth ValuativeRel ℚ_[p]` fails unless
`Mathlib.NumberTheory.Padics.ValuativeRel` is imported explicitly (that file, not
`PadicNumbers.lean`, carries `instance : ValuativeRel ℚ_[p]`, `Padics/ValuativeRel.lean:29`).

With `import Candidates.Nonarchimedean`, the *same two goals* compile with no output
(`Probe2.lean`, scratch, `lake env lean Probe2.lean` → empty, exit 0). That is the A/B proof that
the instance is what does the work.

## 3. How the instance is proved

`ℚ_[p]` is nonarchimedean-normed (`Padic.nonarchimedean`,
`Mathlib/NumberTheory/Padics/PadicNumbers.lean:834`), so `Metric.ball 0 r` is closed under
addition; balls are open (`Metric.isOpen_ball`, `Pseudo/Defs.lean:839`), contain `0`
(`Metric.mem_ball_self`, :382) and are closed under negation. Given `U ∈ 𝓝 0`,
`Metric.mem_nhds_iff` (:779) yields `ball 0 ε ⊆ U`, and
`exists_pow_lt_of_lt_one` (`Mathlib/Algebra/Order/Archimedean/Basic.lean:252`) with
`(p:ℝ)⁻¹ < 1` (`inv_lt_one_of_one_lt₀`, `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:931`)
yields `n` with `(p:ℝ)⁻¹ ^ n < ε`; then `Metric.ball_subset_ball` (:534) closes the subset goal.

## 4. Commands run and their actual output

All run from `candidates/nonarchimedean-ring/`, toolchain `leanprover/lean4:v4.34.0-rc2`
(`lean-toolchain`, Lake `5.0.0-src+6a10ac8`), Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0` (verified with `git rev-parse HEAD` in the mathlib
package, prebuilt oleans present).

```
$ lake env lean Candidates/Nonarchimedean.lean
                       <-- no output at all; diagnostics count = 0; exit 0
```

```
$ lake env lean -Ddiagnostics=true Candidates/Nonarchimedean.lean
[diag] Diagnostics
  [reduction] unfolded reducible declarations (max: 21, num: 1):
    [reduction] outParam ↦ 21
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
[diag] Diagnostics
  [reduction] unfolded declarations (max: 30, num: 1):
    [reduction] LT.lt ↦ 30
  ...
[diag] Diagnostics
  [reduction] unfolded declarations (max: 85, num: 4):
    [reduction] LT.lt ↦ 85
    [reduction] OfNat.ofNat ↦ 30
    [reduction] Zero.zero ↦ 23
    [reduction] LE.le ↦ 21
  [reduction] unfolded reducible declarations (max: 141, num: 4):
    [reduction] inferInstance ↦ 141
    [reduction] Nat.cast ↦ 54
    [reduction] outParam ↦ 51
    [reduction] FunLike ↦ 23
  [kernel] unfolded declarations (max: 26, num: 1):
    [kernel] OfNat.ofNat ↦ 26
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
                       <-- informational counters only; no error, no warning; exit 0
```

```
$ lake env lean -DwarningAsError=true -DautoImplicit=false Candidates/Nonarchimedean.lean
                       <-- no output; exit 0. Warnings-as-errors clean, no autoImplicit reliance.
```

```
$ lake build Candidates
ℹ [1768/1770] Built Candidates.Axioms (14s)
✔ [1769/1770] Built Candidates (14s)
Build completed successfully (1770 jobs).
```

## 5. Axiom audit (`lake env lean Candidates/Axioms.lean`)

Whitelist `{propext, Classical.choice, Quot.sound}` — all nine declarations, no exceptions:

```
'Candidates.Nonarchimedean.instNonarchimedeanRingPadic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.exists_openAddSubgroup_subset_closedBall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Candidates.Nonarchimedean.nonarchimedeanAddGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.norm_add_le_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.isUltrametricDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.hasSum_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.summable_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.tsum_mul_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Candidates.Nonarchimedean.summable_iff_tendsto_cofinite_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

(The line breaks in the second and ninth entries are Lean's own message wrapping.)

Forbidden tokens: `sorry`, `admit`, `axiom `, `opaque`, `native_decide` occur **nowhere** in the
sources — the only grep hits are the two lines of `Candidates/Axioms.lean`'s own docstring that
name the forbidden tokens while promising they are absent.

## 6. What this unblocks

Mathlib's nonarchimedean infinite-sum file binds
`[Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]`
(`InfiniteSum/Nonarchimedean.lean:113`), so **all** of its exports were unusable at `R = ℚ_[p]`:

* `HasSum.mul_of_nonarchimedean` (:126) → `hasSum_mul`
* `Summable.mul_of_nonarchimedean` (:135) → `summable_mul`
* `tsum_mul_tsum_of_nonarchimedean` (:139) → `tsum_mul_tsum`
* `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (:104, the `[to_additive]` of
  `multipliable_iff_tendsto_cofinite_one`) → `summable_iff_tendsto_cofinite_zero`

Why the last two are not obtainable from the general lemmas: the general
`HasSum.mul` (`InfiniteSum/Ring.lean:178`) and `Summable.tsum_mul_tsum` (`:186`) take
`Summable (fun x : ι × κ ↦ f x.1 * g x.2)` **as an extra hypothesis**
(`InfiniteSum/Ring.lean:179`, `:187`), and `tsum_mul_tsum_of_summable_norm`
(`Mathlib/Analysis/Normed/Ring/InfiniteSum.lean:70`) needs `Summable fun x ↦ ‖f x‖` and
`Summable fun x ↦ ‖g x‖` on top of `[CompleteSpace R]`. In a nonarchimedean field plain
`Summable` is strictly weaker than norm-summability, so none of those is a drop-in substitute.
With the instance, product summability is *derived*, not assumed.

## 7. What this does **not** unblock

* **`p`-adic `log`/`exp` is still absent.** That gap (`research/exploration/RESULTS.md:65`,
  row `p-adic log/exp`) is about the analytic series themselves. `NonarchimedeanRing` was never
  the missing ingredient for `log`/`exp`; it was the missing ingredient for the *unconditional
  summability* lemmas those series would be summed with. Closing this instance moves the
  convergence kit from "partly usable" to "usable", and moves the `log`/`exp` gap by nothing.
* **No IUT content.** Nothing here constructs a pilot, a `Θ`-link, an `Ism`, a log-shell, or any
  object of inter-universal Teichmüller theory; it closes one Lean typeclass obligation.
* **The two "consequences" the brief asked for are not consequences of this class.**
  `norm_add_le_max` and `isUltrametricDist` are both stated in
  `Candidates/Nonarchimedean.lean` and both are labelled there: `norm_add_le_max` is
  `Padic.nonarchimedean` (`PadicNumbers.lean:834`) and `isUltrametricDist` is the pre-existing
  unnamed instance `instance : IsUltrametricDist ℚ_[p]` (`PadicNumbers.lean:776`). Neither flows
  through `NonarchimedeanRing`, and no proof of either could: the class constrains the topology,
  not the norm. The genuinely through-the-instance non-vacuity check is
  `exists_openAddSubgroup_subset_closedBall` (the class must hand back an actual subgroup inside
  the closed unit ball) plus `nonarchimedeanAddGroup`.

## 8. Other routes found in Mathlib, and why they do not fire

* `ValuativeRel.nonarchimedeanRing`
  (`Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:69`) already proves
  `NonarchimedeanRing R` for any `[Ring R] [ValuativeRel R]` — but with the topology
  **built from the valuative relation** (`local instance topologicalSpace`, :67), which is not
  `Padic`'s norm topology. `#check @ValuativeRel.nonarchimedeanRing` prints
  `∀ (R : Type u_1) [inst : Ring R] [inst_1 : ValuativeRel R], NonarchimedeanRing R`, and
  `#synth NonarchimedeanRing ℚ_[p]` still fails, confirming the topology argument does not unify.
* `RingSubgroupsBasis.nonarchimedean`
  (`Mathlib/Topology/Algebra/Nonarchimedean/Bases.lean:188`) proves
  `@NonarchimedeanRing A _ hB.topology` — again with the topology taken *from* the basis, so it
  would require proving that basis's topology equals `Padic`'s.
* `AdicTopology` (`…/AdicTopology.lean:246`) is the `I`-adic analogue; not applicable.

## 9. Files

```
candidates/nonarchimedean-ring/
  lakefile.lean                     Lean DSL: package `candidates`, requires mathlib + iut_bridge
  lake-manifest.json                byte-identical copy of candidates/pilot-shadow/lake-manifest.json
  lean-toolchain                    leanprover/lean4:v4.34.0-rc2 (copy)
  Candidates.lean                   imports Candidates.Nonarchimedean, Candidates.Axioms
  Candidates/Nonarchimedean.lean    137 lines: the instance + non-vacuity + use tests
  Candidates/Axioms.lean            26 lines: `#print axioms` for all nine declarations
  README.md                         this file
```

Note on the brief: it asked to copy `candidates/orbit-quotient/lakefile.lean`. That directory does
not exist in this worktree; the only existing candidate is `candidates/pilot-shadow/`, whose
`lakefile.toml` requires `iut_bridge` from `../../bridge` and mathlib from the absolute package
path. This candidate reproduces that exact structure (same package name `candidates`, same
requires, same manifest) but writes it as `lakefile.lean` in the Lake Lean DSL. `iut_bridge` is
required but not imported, so no build of `bridge/` or `local-field/` is triggered
(`lake build Candidates` completed without building them).
