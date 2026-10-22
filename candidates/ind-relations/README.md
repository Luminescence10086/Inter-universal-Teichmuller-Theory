# `candidates/ind-relations` — relation-valued Ind1–Ind3 allowed operations

MR candidate for the first item of the "next three goals" table in
[`research/exploration/correspondence.md`](../../research/exploration/correspondence.md)
(§*下一步三个目标*, rank 1) and for RI-01/RI-04/RI-05 of
[`research/round3-realization-obligations.md`](../../research/round3-realization-obligations.md):

> Ind1–Ind3 as **relation-valued** allowed operations + projection equation.
> Must keep: Ind3 is a relation, not a group action; `Allowed12` strictly smaller than all
> of `A(k)`; `CompositionClosed` is a target to be proved, not an assumption.

This directory contains **no** Θ-link, **no** `Ism`, **no** Kummer element, **no** Cor 3.12,
and closes no gap in any argument about IUT. What it does contain is the shape: an explicit
relation on actual p-adic tuples, an explicit inclusion theorem into the ambient `A(k)`
family, an explicit **strictness** witness, an explicit **conditional** composition-closure
theorem, and a proof that the raw generator family is **not** composition closed.

## Files

| path | role |
|---|---|
| `lakefile.lean` | Lake package `ind_relations`, requires `../../bridge` and the worktree Mathlib lock |
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` (same as `bridge/`) |
| `Candidates.lean` | library root |
| `Candidates/IndRelations.lean` | the model and all theorems (359 lines) |
| `Candidates/Axioms.lean` | `#print axioms` audit for all 25 results |

Two notes on the requested structure:

* `candidates/orbit-quotient` **does not exist in this worktree** (branch `explore/ind`; it
  lives only on `task/m2`). The structure was therefore copied from
  `candidates/pilot-shadow`, the only candidate present here, and it is the same shape.
* `lakefile.lean` vs `lakefile.toml`: both reference candidates use `lakefile.toml`. As
  requested, this candidate is a **`lakefile.lean`**. It must say

  ```lean
  require iut_bridge from "../../bridge"
  ```

  and not `require bridge from "../../bridge"`: Lake binds a required package under the
  package name *declared in the required directory*, and `bridge/lakefile.toml` declares
  `name = "iut_bridge"`. The literal `require bridge from "../../bridge"` is **rejected**
  (`error: dependency 'bridge' not in manifest; use 'lake update bridge' to add it`), which
  was verified before writing the final form. `bridge` is required for the shared Mathlib
  lock; `Candidates/IndRelations.lean` imports only Mathlib (no `IUTBridge.*` module), so the
  candidate does not depend on unbuilt bridge artifacts.

## The model, in one screen

```lean
abbrev Tuple (p : ℕ) [Fact p.Prime] : Type := Fin 4 → ℚ_[p]

def relabel (σ : Equiv.Perm (Fin 4)) (x : Tuple p) : Tuple p := fun i => x (σ.symm i)
def scale   (a : Fin 4 → ℚ_[p]ˣ)    (x : Tuple p) : Tuple p := fun i => (a i : ℚ_[p]) * x i
def pull    (τ : Equiv.Perm (Fin 4)) (a : Fin 4 → ℚ_[p]ˣ)   := fun k => a (τ k)
def move    (σ : Equiv.Perm (Fin 4)) (a : Fin 4 → ℚ_[p]ˣ) (x : Tuple p) := relabel σ (scale a x)
def e (i : Fin 4) : Tuple p := Pi.single i (1 : ℚ_[p])          -- slot unit vector

def Gamma12 : List (Equiv.Perm (Fin 4))     := [1, Equiv.swap 0 1]      -- finite relabellings
def flip0   : Fin 4 → ℚ_[p]ˣ                := fun i => if i = 0 then -1 else 1
def S       : List (Fin 4 → ℚ_[p]ˣ)         := [1, flip0]              -- finite slotwise scalings

def Allowed12 (x y : Tuple p) : Prop := ∃ σ ∈ Gamma12, ∃ a ∈ S, y = move σ a x
def ambient   (x y : Tuple p) : Prop := ∃ σ : Equiv.Perm (Fin 4), ∃ a : Fin 4 → ℚ_[p]ˣ,
                                          y = move σ a x
def CompositionClosed (ℛ : Tuple p → Tuple p → Prop) : Prop :=
  ∀ x y z, ℛ x y → ℛ y z → ℛ x z
```

`S` is *a finite value set `{±1} ⊆ ℚ_[p]^×` plus a slot profile `{0}`*: slot `0` may be
scaled by `±1`, every other slot carries `1`. `Γ12` is a genuine subgroup of `S₄` of order
two. `Allowed12` is `∃`-valued: **not** a function, **not** a group action, and it never
identifies its generators with elements of one monoid of isomorphisms (ledger F-01).

## Exact statements

Reproduced verbatim from `Candidates/IndRelations.lean` (`p : ℕ`, `[Fact p.Prime]` implicit
throughout).

| # | name | statement |
|---|---|---|
| 1 | `relabel_relabel` | `relabel ρ (relabel σ x) = relabel (σ.trans ρ) x` |
| 2 | `scale_scale` | `scale a (scale b x) = scale (a * b) x` |
| 3 | `scale_relabel` | `scale a (relabel σ y) = relabel σ (scale (pull σ a) y)` |
| 4 | `relabel_single` | `relabel σ (Pi.single i c : Tuple p) = (Pi.single (σ i) c : Tuple p)` |
| 5 | `scale_single` | `scale a (Pi.single i c : Tuple p) = (Pi.single i ((a i : ℚ_[p]) * c) : Tuple p)` |
| 6 | `move_e` | `move σ a (e i) = (Pi.single (σ i) ((a i : ℚ_[p])) : Tuple p)` |
| 7 | `neg_e` | `(-(e i) : Tuple p) = (Pi.single i (-1 : ℚ_[p]) : Tuple p)` |
| 8 | `move_apply` | `move σ a x i = (a (σ.symm i) : ℚ_[p]) * x (σ.symm i)` |
| 9 | **`move_projection`** | `move σ a x (σ j) = (a j : ℚ_[p]) * x j` |
| 10 | **`move_projection_source`** | `move σ (pull σ a) x (σ j) = (a (σ j) : ℚ_[p]) * x j` |
| 11 | `move_move` | `move ρ b (move σ a x) = move (σ.trans ρ) (pull σ b * a) x` |
| 12 | `mem_Gamma12` | `σ ∈ Gamma12 ↔ σ = 1 ∨ σ = Equiv.swap 0 1` |
| 13 | `gamma12_trans_mem` | `∀ σ ∈ Gamma12, ∀ ρ ∈ Gamma12, σ.trans ρ ∈ Gamma12` |
| 14 | `mem_S` | `a ∈ S ↔ a = 1 ∨ a = flip0` |
| 15 | `flip0_val_zero` / `flip0_val_one` | `(flip0 0 : ℚ_[p]) = -1`, `(flip0 1 : ℚ_[p]) = 1` |
| 16 | **`allowed12_subset`** | `Allowed12 x y → ambient x y` (for all `x y`) |
| 17 | `ambient_e3_e2` | `ambient (e 3) (e 2)` |
| 18 | **`not_allowed12_e3_e2`** | `¬ Allowed12 (e 3) (e 2)` |
| 19 | **`allowed12_strict`** | `∃ x y, ambient x y ∧ ¬ Allowed12 x y` |
| 20 | **`compositionClosed_of_closed`** | `(∀ σ ∈ Gamma12, ∀ ρ ∈ Gamma12, σ.trans ρ ∈ Gamma12) → (∀ σ ∈ Gamma12, ∀ a ∈ S, ∀ b ∈ S, pull σ b * a ∈ S) → CompositionClosed Allowed12` |
| 21 | `not_scaling_family_closed` | `¬ (∀ σ ∈ Gamma12, ∀ a ∈ S, ∀ b ∈ S, pull σ b * a ∈ S)` |
| 22 | **`not_compositionClosed`** | `¬ CompositionClosed Allowed12` |
| 23 | `neg_one_ne_one` / `neg_one_ne_zero` | `(-1 : ℚ_[p]) ≠ 1`, `(-1 : ℚ_[p]) ≠ 0` |

### Faithful vs toy

| aspect | status |
|---|---|
| relation-valued `Allowed12` (`∃` generator + `∃` scalars + equation) | **faithful** to the ledger's required shape (RI-01/RI-05, F-01 avoided) |
| `allowed12_subset` as a theorem, not a definition | **faithful** |
| `allowed12_strict` with explicit witness | **faithful** (the ledger's "strictly smaller" requirement) |
| `CompositionClosed` as a hypothesis-taking target plus a *proved failure* | **faithful** (closure is never assumed) |
| projection equation as a coordinate identity | **faithful** in form |
| tuple type `Fin 4 → ℚ_[p]` | **toy**: slot layer only, no Hodge theater, `Fin 4` is not a real slot set |
| `Γ12 = {1, swap 0 1}` | **toy**: not the Ind1 procession; the real label action is not `Equiv.Perm (Fin 4)` (cf. C-01) |
| `S = {1, flip0}` | **toy**: a finite value set × slot profile, not `Adm(c)` of a real Kummer choice |
| no Θ-link / `Ism` / Cor 3.12 | as required: none attempted |

## Strictness witness (the safety property)

`allowed12_strict` is proved from two explicit theorems:

* source `x = e 3`, i.e. the coordinate profile `(0,0,0,1)`;
* target `y = e 2`, i.e. the coordinate profile `(0,0,1,0)`;
* **`ambient (e 3) (e 2)`** holds via the generator `(swap 2 3, 1)`: `move (swap 2 3) 1 (e 3)`
  is `Pi.single ((swap 2 3) 3) 1 = Pi.single 2 1 = e 2`.
* **`¬ Allowed12 (e 3) (e 2)`**: for any `σ ∈ Γ12` we have `σ 3 = 3` (both `1` and
  `swap 0 1` fix slot `3`) and for any `a ∈ S` we have `(a 3 : ℚ_[p]) = 1` (`flip0` scales
  slot `0`, not slot `3`). Hence every allowed image of `e 3` is `e 3`, and coordinate `3`
  gives `0 = 1`.

**Which coordinate profile makes it fail.** Slot `3` is outside both the relabelling support
and the scaling profile, so its value is preserved *exactly* by `Allowed12`; the ambient
`A(k)` family can permute it away. The witness is therefore a single-slot exactness
statement: `(0,0,0,1)` is allowed-reachable only from `(0,0,0,1)`, while `(0,0,1,0)` is
ambient-reachable from it and allowed-unreachable.

## Composition-closure status

Closure is proved **conditionally** and refuted **unconditionally for the raw family**; it is
never assumed.

* `compositionClosed_of_closed` takes exactly the two hypotheses written in statement 20.
* The `Γ12` hypothesis is **discharged**: `gamma12_trans_mem`.
* The `S` hypothesis is **refuted**: `not_scaling_family_closed` — with `σ = swap 0 1`,
  `a = 1`, `b = flip0` the composite scalar `pull (swap 0 1) flip0 * 1` is the flip of slot
  `1`, which is not in `S`.
* `not_compositionClosed` gives the unconditional failure. Witness:
  `x = e 1`, `y = e 0`, `z = -e 1`;
  `Allowed12 (e 1) (e 0)` via `(swap 0 1, 1)` (this is `move_e` with `(swap 0 1) 1 = 0`);
  `Allowed12 (e 0) (-e 1)` via `(swap 0 1, flip0)` (`move_e` gives `Pi.single 1 (-1) = -e 1`
  by `neg_e`); but `¬ Allowed12 (e 1) (-e 1)`, because every allowed image of `e 1` is
  `e 0` or `e 1` and coordinate `1` of `-e 1` is `-1 ≠ 1` and `-1 ≠ 0`.

So the composition of two allowed moves *is* a move along the composite permutation, but its
scalar family `pull σ b * a` need not lie in the finite set `S`. That is a real obstruction,
not a modelling artefact: it is exactly why closure must be a target with hypotheses.

## The projection equation, as literally proved

```lean
theorem move_projection (σ : Equiv.Perm (Fin 4)) (a : Fin 4 → ℚ_[p]ˣ) (x : Tuple p)
    (j : Fin 4) : move σ a x (σ j) = (a j : ℚ_[p]) * x j
theorem move_projection_source (σ : Equiv.Perm (Fin 4)) (a : Fin 4 → ℚ_[p]ˣ) (x : Tuple p)
    (j : Fin 4) : move σ (pull σ a) x (σ j) = (a (σ j) : ℚ_[p]) * x j
theorem move_apply (σ) (a) (x) (i) : move σ a x i = (a (σ.symm i) : ℚ_[p]) * x (σ.symm i)
```

with the convention `relabel σ x i = x (σ.symm i)` (so `σ` really does move the content of
slot `j` to slot `σ j`). The ledger's literal form
`(relabel σ (scale a x)) (σ j) = a (σ j) * x j` is **not** the correct statement for a single
target-indexed scalar family; it holds for the source-indexed family `pull σ a`, which is
statement 10. See finding F‑1 below.

## Verification (exact commands)

Run from `candidates/ind-relations/`:

```powershell
lake build                                  # -> "Build completed successfully (1754 jobs)"
lake env lean Candidates/IndRelations.lean   # -> no output, exit 0
lake env lean Candidates/Axioms.lean         # -> 25 #print axioms lines, exit 0
```

Diagnostics count: **0** for `Candidates/IndRelations.lean` (0 errors, 0 warnings; the
command prints nothing and exits 0) and **0** for `Candidates/Axioms.lean` (only the 25
`#print axioms` info lines). `lake build` reports no diagnostics from this package.

The one Lake message seen on a *cold* Lakefile elaboration —
`Warning: your project pins different versions of some dependencies than Mathlib` — is a Lake
dependency-pin note about the shared external Mathlib checkout (the same one
`candidates/pilot-shadow` and `bridge/` produce), not a Lean diagnostic about this file; it
does not reappear as a per-file diagnostic.

## `#print axioms`, per theorem

All 25 results were printed by `lake env lean Candidates/Axioms.lean`, and every one reports
exactly the allowed set:

```
'Candidates.IndRelations.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

for each of: `neg_one_ne_one`, `neg_one_ne_zero`, `relabel_relabel`, `scale_scale`,
`scale_relabel`, `relabel_single`, `scale_single`, `move_e`, `neg_e`, `move_apply`,
`move_projection`, `move_projection_source`, `move_move`, `mem_Gamma12`,
`gamma12_trans_mem`, `mem_S`, `flip0_val_zero`, `flip0_val_one`, `allowed12_subset`,
`ambient_e3_e2`, `not_allowed12_e3_e2`, `allowed12_strict`, `compositionClosed_of_closed`,
`not_scaling_family_closed`, `not_compositionClosed`.

No theorem uses any axiom outside `{propext, Classical.choice, Quot.sound}`; nothing depends
on `sorryAx`.

## Forbidden-token grep

```powershell
Get-ChildItem -Recurse -Filter *.lean |
  Select-String -Pattern 'sorry|admit|axiom|opaque|native_decide'
```

| file | matches |
|---|---|
| `Candidates/IndRelations.lean` | **0** |
| `Candidates.lean` | **0** |
| `lakefile.lean` | **0** |
| `Candidates/Axioms.lean` | 28 — all of them the string `axioms` inside the 25 `#print axioms` audit commands plus its own docstring; **0** occurrences of `sorry`, `admit`, `opaque`, `native_decide` |

Word-boundary form `\baxiom\b` over all `.lean` files in this directory: **0 matches** (the
audit command is spelled `#print axioms`, which the word-boundary pattern does not match).
There is no `sorry`, no `admit`, no locally declared axiom, no `opaque`, no `native_decide`,
no `implemented_by`, no `extern`.

## Findings

**F‑1 (correction of the ledger's English).** The projection equation as written in
correspondence.md rank‑1 ("`(relabel σ (scale a x)) (σ j) = a (σ j) * x j`") is not a theorem
for one target-indexed scalar family: with the convention that `σ` moves slot `j` to `σ j`,
the true identity is `(a j) * x j` (statement 9). The literal form is recovered only after
transporting the scalars to the source slots, i.e. with `pull σ a` (statement 10). The two
forms differ by the permutation `σ` acting on the scalar index; a formalisation that keeps
the ledger's phrase verbatim would be **false**.

**F‑2 (the closure hypothesis is not "S closed under pointwise product").** The honest
hypothesis is closure under `pull σ b * a` — the *outer* scalar reindexed by `σ`, times the
inner scalar — because a two-generator composite carries the permutation and the scalars
together (statement 11). The ledger's phrasing ("`Γ12` closed under the composition rule +
`S` closed under pointwise product") understates the requirement: `Γ12` can be a genuine
subgroup and `S` can be pointwise-product closed, yet closure still fail, because
`pull σ b` need not stay in `S`. In the toy model this is not hypothetical:
`gamma12_trans_mem` holds while `not_scaling_family_closed` refutes the scalar side.

**F‑3 (composition closure fails here, and that is the interesting outcome).** For the raw
generator family `¬ CompositionClosed Allowed12` (statement 22). The model therefore does not
silently upgrade a relation-valued family to a monoid: closure has to be *earned* by an
enlarged scalar family, and enlarging `S` towards "all nonzero slotwise scalars" is exactly
the move that would eat the strictness witness (F‑4). Any future claim of Ind1–Ind3
composition closure must exhibit the enlarged family **and** re-prove strictness against
`A(k)`.

**F‑4 (strictness is an exactness property, not a counting property).** `Allowed12` is
strictly smaller than `ambient` for a *coordinate-profile* reason: slots outside the
relabelling support and outside the scaling profile keep their value exactly. This suggests
that in the real setting strictness should be certified by an invariant of the allowed
operations (a slot value that no generator can touch), not by counting generators — counting
would be destroyed by any harmless enlargement of the family.

**F‑5 (convention dependence).** The composition rule's order (`σ.trans ρ`, with `σ` the
inner and `ρ` the outer generator) is a consequence of the convention
`relabel σ x i = x (σ.symm i)`. With the opposite convention the rule reads `ρ.trans σ`.
The ledger does not fix this convention, and a verbatim import of its formulas into a proof
assistant is order-ambiguous; `move_move` (statement 11) fixes one convention explicitly.

**F‑6 (environment notes).** (i) `candidates/orbit-quotient` is absent from this worktree, so
`candidates/pilot-shadow` supplied the package structure; (ii) Lake refuses
`require bridge from "../../bridge"` and requires the declared name `iut_bridge`; (iii) the
toy type must be written `Tuple p` with the `Fact p.Prime` instance as an `abbrev` parameter
(`abbrev Tuple (p : ℕ) [Fact p.Prime] : Type := Fin 4 → ℚ_[p]`) — `Padic p` alone does not
elaborate without the instance.

## VERDICT

`VERDICT: CORE_PROVED`

Meaning of the verdict: every statement this candidate claims is proved with zero `sorry`,
using only `{propext, Classical.choice, Quot.sound}`; the relation-valued `Allowed12`, the
inclusion theorem, the strictness witness, the conditional closure theorem and the collapse
of the raw family's closure are all fully proved; the algebra is on actual `ℚ_[p]` tuples.
The verdict is about **the core relation-valued shape and its safety properties** — it is
not, and cannot be, a claim about Ind1/Ind2/Ind3 themselves, about `Ism`, about the Θ-link,
or about Cor 3.12, none of which is modelled here.
