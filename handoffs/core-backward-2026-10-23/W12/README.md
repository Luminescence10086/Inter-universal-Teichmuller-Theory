# W12 — `LabelNormalization.lean` (M-iii toy: `|F_l|`-index vs `F_l^⋆`-average)

Date: 2026-10-23. Deliverable: **one** new file, `candidates/core-transport/LabelNormalization.lean`.
No existing file, `tools/`, fact-tree, registry or other candidate was modified.

## Scope

The obligation is `research/core-backward-2026-10-23/h3-prerequisites.md` §M-iii, item 1 of 要补的证明: the
source averages over `j ∈ F_l^⋆` (IUT III, Step (x), txt 10904–10922) but (xi-d) (txt 11022) indexes by
`j ∈ |F_l|`, and IUT II, Corollary 4.10, (i) (txt 7003–7010) identifies the label `0` with `⟨F_l^⋆⟩`. This
file formalises **when those two indexings are forced to give the same number**: exactly when the labels are
the orbit, i.e. when `g ↦ g • base` is a bijection `G → Lab`.

Contents, in order:

| declaration | content |
|---|---|
| `averageOverLabels` | `(∑ l : Lab, f l) / card Lab` — the `\|F_l\|`-indexed normalization |
| `averageOverOrbit G base` | `(∑ g : G, f (g • base)) / card G` — the `F_l^⋆`-average |
| `InvariantReading G f` | `∀ a l, f (a • l) = f l` |
| `card_eq_card_of_bijective` | `card G = card Lab` via `Fintype.card_congr` |
| `sum_over_labels_eq_sum_over_orbit` | numerator equality by `Fintype.sum_bijective` (no invariance used) |
| `averageOverLabels_eq_averageOverOrbit` | **main identity**, for every reading |
| `card_cast_ne_zero`, `sum_orbit_eq_card_mul`, `averageOverOrbit_eq_base_of_invariant`, `coord_at_base` | W5 recovered as a corollary (invariant reading ⇒ average = value at `base`) |
| `ToyLab`/`ToyGroup`/`toyReading` + 8 toy lemmas | anti-degeneracy with computed numbers |

Simple transitivity is encoded as a **hypothesis on an existing `MulAction`**, not as a new structure:
`hAct : Function.Bijective (fun g : G => g • base)`. That keeps the two normalizations defined for *any*
`MulAction`, so the anti-degeneracy can drop `hAct` and use exactly the same definitions.

Exact statements (from `#print`):

```
theorem averageOverLabels_eq_averageOverOrbit :
  ∀ {Lab} [Fintype Lab] {G} [Group G] [Fintype G] [MulAction G Lab] (base : Lab),
    (Function.Bijective fun g => g • base) →
      ∀ (f : Lab → ℚ_[3]), averageOverLabels f = averageOverOrbit G base f

theorem coord_at_base :
  ∀ {Lab} [Fintype Lab] {G} [Group G] [Fintype G] [MulAction G Lab] (base : Lab),
    (Function.Bijective fun g => g • base) →
      ∀ {f : Lab → ℚ_[3]}, InvariantReading G f → averageOverLabels f = f base
```

## Anti-degeneracy (item 5), computed

Labels `ToyLab := ZMod 3`, group `ToyGroup := (ZMod 3)ˣ` (two units, acting by multiplication), base `0`.
The unit `-1` swaps the labels `1` and `2` and fixes `0`, so the orbit of `0` is `{0} ⊊ ToyLab`: the labels
are **not** the orbit. Reading `toyReading` takes `1, 2, 3` at `0, 1, 2`.

* `toyGroup_card : card ToyGroup = 2`, `toyLab_card : card ToyLab = 3`
* `toy_not_bijective : ¬ Function.Bijective (fun u : ToyGroup => u • 0)` (it would force `2 = 3`)
* `averageOverLabels_toyReading : averageOverLabels toyReading = 2`  (`= (1+2+3)/3`)
* `averageOverOrbit_toyReading : averageOverOrbit ToyGroup 0 toyReading = 1`  (`= (1+1)/2`)
* `toy_averages_differ : averageOverLabels toyReading ≠ averageOverOrbit ToyGroup 0 toyReading`
* `averageOverOrbit_eq_value_at_base : averageOverOrbit ToyGroup 0 toyReading = toyReading 0`

i.e. the two values are `2` and `1`, and the orbit half is exact *without* `hAct` because `0` is fixed —
what the bijectivity hypothesis buys is the **label** half.

## Commands and results

```
cd candidates/core-transport
lake env lean -DwarningAsError=true LabelNormalization.lean
```

* exit code **0**, **stderr 0 bytes**, stdout 2939 bytes (`build.stdout.log`, 30 dependency lines)
* file: 21 912 bytes, 366 newlines
* sha256 `5D711C6FE88BE8B3B23258EB944A22BDA6A68D55F9FBFE262B60B9CB8E5DCCB1`
* forbidden-substring scan (whole file, docstrings included): `sorry` 0, `admit` 0, `opaque` 0,
  `native_decide` 0. The string `axiom` occurs exactly 30 times, all of them inside the 30 `#print axioms`
  commands required by the task; outside those commands the count is 0.
* machine-checked summary: `checks.txt`; raw build output: `build.stdout.log`, `build.stderr.log`

## Dependency footprint

All 30 declarations carry a `#print axioms` line. Verbatim shape of every line, one per declaration:

```
'LabelNormalization.averageOverLabels' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'LabelNormalization.ToyLab' does not depend on any axioms
```

No declaration depends on anything outside `{propext, Classical.choice, Quot.sound}`: 29 lines report those
three, and exactly one line — `ToyLab` — reports no dependency at all (`ToyGroup`, as an `abbrev` for
`(ZMod 3)ˣ`, unfolds through instances and reports the same three). The full list is `build.stdout.log`.

## Non-claims

1. The file does **not** identify the source's `|F_l|` with `F_l^⋆`. It proves the conditional: *if* the
   labels are the orbit *then* the two indexings agree; *if* they are not *then* they can differ. Whether
   (xi-d) actually uses the procession convention stays a definition alignment in the source.
2. It is a toy on a finite label set with an abstract finite group: `ToyLab` is `ZMod 3`, `ToyGroup` its
   unit group, not the label group of a number field, and the reading is an arbitrary function into
   `ℚ_[3]`, not a log-volume.
3. No procession, capsule, theta value, theta-link, F-prime-strip, Frobenioid, log-volume, log-shell,
   Hodge theater, coricity, poly-isomorphism or `Ind1`/`Ind2`/`Ind3` occurs. The source's claim that the
   procession-normalized volume is (Ind1)(Ind2)-invariant and bounds (Ind3) is untouched.
4. `ℚ_[3]` is used only as a commutative field (the ring the earlier provinces read in); the norm,
   valuation and logarithm series do not occur here.
5. The main identity is weak by design — no property of the reading enters it — so it must not be quoted as
   an averaging theorem with analytic content. Invariance only enters in `coord_at_base`, where it forces
   constancy on the orbit.
6. Nothing from the other toy files (`NormalizationAlignment.lean` etc.) is imported: they are not Lake
   modules, no `olean` of them exists, and `import` of them is unavailable. The three definitions needed
   were restated here; the only import is `CoreLog.QpThree`.

## Repair log (2 rounds, both on a draft kept outside the deliverable path)

1. Round 1 (draft): implicit `G` in `averageOverOrbit` was not determinable from `base`/`f` (typeclass
   `MulAction ?m Lab` stuck), one unused section variable, three small tactic issues. Fix: `G` made an
   explicit argument of both `averageOverOrbit` and `InvariantReading`; sections split so no auto-included
   variable is unused; `first | norm_num | ...` replaced by plain `norm_num`; one `simp` argument dropped.
2. Round 2 (draft): exit 0. The file was then copied to the deliverable path, where the exact command above
   was run again with exit 0 and empty stderr. No failing proof was ever left at the deliverable path.
