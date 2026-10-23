import CoreLog.QpThree

/-!
# W12 toy: the label-indexed normalization and the orbit average coincide exactly when the labels are the
orbit

**Scope.** This file formalises one algebraic identity, one corollary of it, and one concrete failure of
the identity once its hypothesis is dropped. The carrier is a finite label set `Lab`, a finite group `G`
acting on `Lab` through a `MulAction`, a base label `base : Lab`, and readings `f : Lab → ℚ_[3]`. Nothing
else is formalised: no topology, no logarithm series, no norm, no structure beyond `Fintype`, `Group`,
`MulAction` and the commutative field `ℚ_[3]`.

**The two normalizations.** The source normalises a reading in two places in two syntactically different
ways. In the procession normalization of IUT III, Step (x) (txt 10904–10922) the average is taken over
`j ∈ F_l^⋆`, a *group*. In (xi-d) (txt 11022) the log-volume is indexed by `j ∈ |F_l|`, a *label set*. The
two are:
* `averageOverLabels f = (∑ l : Lab, f l) / (card Lab)` — the `|F_l|`-indexed normalization;
* `averageOverOrbit G base f = (∑ g : G, f (g • base)) / (card G)` — the `F_l^⋆`-average along the orbit of
  the base label.

**The hypothesis, and how it is encoded.** The source's alignment (IUT II, Corollary 4.10, (i), txt
7003–7010) identifies the collections of data `Ψcns(F)_0` and `Ψcns(F)_{⟨F_l^⋆⟩}`, i.e. it says the label
`0` *is* the orbit `⟨F_l^⋆⟩`. The hypothesis that turns that slogan into mathematics is **simple
transitivity through `base`**: the map `g ↦ g • base` is a bijection `G → Lab`, encoded as the hypothesis
`hAct : Function.Bijective (fun g : G => g • base)` on the given `MulAction`. This is the statement that
the labels are the orbit — each label is `g • base` for exactly one `g`, so there are exactly as many
labels as group elements and each label is hit once. It is stated as a hypothesis rather than as a
structure, so that the anti-degeneracy below can drop it and keep the same definitions.

**What is proved, in order.**
* `averageOverLabels`, `averageOverOrbit` — the two normalizations, both in `ℚ_[3]`. `G` is an explicit
  argument of `averageOverOrbit` because it does not occur in the type of the reading (a reading is a
  function on the label set), so it has to be said which group is being averaged over.
* `InvariantReading` — the hypothesis "the reading does not see which representative of the orbit is
  used", `f (a • l) = f l`.
* `card_eq_card_of_bijective` — the two denominator cardinalities agree, by `Fintype.card_congr` applied
  to `Equiv.ofBijective`.
* `sum_over_labels_eq_sum_over_orbit` — the numerators agree: the sum over the label set is the sum over
  the group indexed along the orbit. This is the reindexing step (`Fintype.sum_bijective`, the `Finset`
  version cited by the task), and it needs no invariance.
* `averageOverLabels_eq_averageOverOrbit` — **the deliverable identity**: under `hAct`, the two
  normalizations are equal for *every* reading. Note what this does and does not use: numerator equality is
  pure reindexing, denominator equality is `card_congr`, and no property of the reading enters. The
  identity is therefore a statement about the *indexings*, not about the reading — which is exactly the
  content of "the labels are the orbit".
* `card_cast_ne_zero`, `sum_orbit_eq_card_mul`, `averageOverOrbit_eq_base_of_invariant`, `coord_at_base`
  — the W5 result recovered here as a corollary of the identity: for an invariant reading, averaging (over
  the labels, and over the orbit) is evaluation at the base label.
* **Anti-degeneracy (item 5)**: `ToyLab := ZMod 3` (three labels), `ToyGroup := (ZMod 3)ˣ` (the two units,
  acting by multiplication), base label `0`. This is the smallest faithful shape of "the labels are not
  the orbit": the units swap the labels `1` and `2` and fix `0`, so the orbit of `0` is `{0}`, a proper
  subset of the three labels. Then `toyGroup_card` is `2` while `toyLab_card` is `3`, `toy_not_bijective`
  says `g ↦ g • 0` is not a bijection (so `hAct` genuinely fails), and for the concrete reading
  `toyReading` with values `1, 2, 3` at the labels `0, 1, 2` the two normalizations are computed:
  `averageOverLabels_toyReading` gives `(1 + 2 + 3) / 3 = 2`, `averageOverOrbit_toyReading` gives
  `(1 + 1) / 2 = 1`, and `toy_averages_differ` separates them, `2 ≠ 1`. The two numbers are computed, not
  asserted, and `averageOverOrbit_eq_value_at_base` records that the orbit average is the value at the
  base label here — the orbit side is exact because `0` is fixed; it is the label side that fails.

**What this file does not say.** It is a toy, and the following are outside it.
1. It does **not** identify the source's `|F_l|` with `F_l^⋆`. Whether (xi-d)'s index `j ∈ |F_l|` is the
   same convention as the `F_l^⋆`-average of Step (x) is a *definition alignment* in the source
   (`research/core-backward-2026-10-23/h3-prerequisites.md`, §M-iii, item 1 of 要补的证明), supported by
   IUT II, Corollary 4.10, (i) and IUT III, txt 10917–10922. What is proved here is the conditional: **if**
   the labels are the orbit **then** the two indexings give the same number, and **if** they are not (the
   anti-degeneracy) **then** they can differ. That is a statement about when such an identification would
   be forced, not an identification.
2. It does not say the identification holds in the source's setting. In the anti-degeneracy, the labels
   are `ZMod 3` and the group is its unit group; that is a toy model of "a group acting on a label set with
   a fixed label", not the label group of a number field.
3. No procession, capsule, theta value, theta-link, `F_l^⋆`, `|F_l|`, `⟨F_l^⋆⟩`, F-prime-strip,
   Frobenioid, log-volume, log-shell, Hodge theater, coricity, poly-isomorphism, `Ism` or `Ind1`/`Ind2`/
   `Ind3` occurs in this file. In particular the file says nothing about (Ind1)–(Ind3), so it does not
   reproduce the source's claim that the procession-normalized volume is invariant under (Ind1), (Ind2) and
   bounded under (Ind3); that claim is not touched.
4. It says nothing about `ℚ_[3]` beyond its commutative field structure: the norm, the valuation, the
   logarithm series and the principal-unit bounds of the other provinces do not occur here. `ℚ_[3]` is used
   only because it is the field in which the earlier provinces read their log-volumes, so the two averages
   are stated in the same ring; nothing here depends on `3` being prime beyond the field structure.
5. It is not evidence for or against any IUT claim. The core GAP of
   `research/core-backward-2026-10-23/h3-prerequisites.md` stays OPEN: `M`-uniqueness (M-i, M-ii) and the
   two unwritten normalizations (M-iii) are untouched, and item 1 above is precisely the obligation this
   file does *not* discharge.
6. The identity `averageOverLabels_eq_averageOverOrbit` is deliberately weak in one direction: because no
   property of the reading enters it, it must not be quoted as an averaging theorem with analytic content.
   Its whole content is that a bijective orbit map lets a sum over labels be rewritten as a sum over the
   group. The corollary `coord_at_base` is where invariance enters, and there the hypothesis is strong:
   invariance forces the reading to be constant on the orbit, so the average collapses to the value at
   `base` rather than being computed from non-constant data.

**Why nothing is imported from the other toy files.** `NormalizationAlignment.lean`,
`ReadingInvariance.lean`, `TransitionCompatibility.lean` and the remaining toy files are top-level modules
of this directory, not modules of the package: `lakefile.lean` declares a single library, `lean_lib
CoreTransport`, whose modules are the ones under `CoreTransport/`, so those files are not Lake targets, no
`olean` of them exists and none is importable. Nothing from them is needed: the two normalizations and the
invariance hypothesis are restated here from scratch (they are three definitions and are cheaper to
restate than to depend on), and the only import is `CoreLog.QpThree`, which supplies the notation `ℚ_[3]`
and Mathlib's field structure on it.

A dependency-footprint block at the end of the file records, for every declaration below, that its only
dependencies are `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LabelNormalization

noncomputable section

/-! ## 1. The two normalizations of a reading -/

/-- **The `|F_l|`-indexed normalization**: the reading is summed over the label set and divided by the
number of labels. This is the shape of (xi-d) (IUT III, txt 11022), "suitably normalized, with respect to
`j ∈ |F_l|`", with the labels playing the role of `|F_l|`. The division is by `card Lab` cast to `ℚ_[3]`;
`card_cast_ne_zero` below is the nonzero-ness that the cancellation in `coord_at_base` consumes. -/
def averageOverLabels {Lab : Type*} [Fintype Lab] (f : Lab → ℚ_[3]) : ℚ_[3] :=
  (∑ l : Lab, f l) / (Fintype.card Lab : ℚ_[3])

/-- **The `F_l^⋆`-average**: the reading is summed over the group `G` along the orbit of a base label, and
divided by the number of group elements. This is the shape of the procession normalization of IUT III,
Step (x) (txt 10904–10922): "the average is taken over `j ∈ F_l^⋆`". The base label `base` stands for the
label `0` which IUT II, Corollary 4.10, (i) identifies with `⟨F_l^⋆⟩`. The group `G` is an explicit
argument: it does not occur in the type of the reading, so nothing else could determine it. -/
def averageOverOrbit (G : Type*) [Group G] {Lab : Type*} [Fintype G] [MulAction G Lab]
    (base : Lab) (f : Lab → ℚ_[3]) : ℚ_[3] :=
  (∑ g : G, f (g • base)) / (Fintype.card G : ℚ_[3])

/-! ## 2. Invariance of the reading under the label action

`G` is an explicit argument of the definition for the same reason as in `averageOverOrbit`. -/

/-- **The reading is invariant under the label action**: it gives the same value at `a • l` as at `l`, i.e.
it does not see which representative of the orbit is used. This is the hypothesis of
`sum_orbit_eq_card_mul`, `averageOverOrbit_eq_base_of_invariant` and `coord_at_base`. -/
def InvariantReading (G : Type*) [Group G] {Lab : Type*} [MulAction G Lab]
    (f : Lab → ℚ_[3]) : Prop :=
  ∀ (a : G) (l : Lab), f (a • l) = f l

/-! ## 3. The identity: the two normalizations coincide when the labels are the orbit -/

section Reindexing

variable {Lab : Type*} [Fintype Lab] {G : Type*} [Group G] [Fintype G] [MulAction G Lab]
  (base : Lab)

/-- **The denominators agree**: the label set and the group have the same number of elements, because
`g ↦ g • base` is a bijection. This is the `Fintype.card_congr` half of the identity, and it is where
"there are as many labels as group elements" is used. -/
theorem card_eq_card_of_bijective (hAct : Function.Bijective (fun g : G => g • base)) :
    Fintype.card G = Fintype.card Lab :=
  Fintype.card_congr (Equiv.ofBijective (fun g : G => g • base) hAct)

/-- **The numerators agree**: the sum over the label set is the sum over the group taken along the orbit.
This is a pure change of indexing variables along the bijection `g ↦ g • base` — the `Finset.sum_bijective`
step of the task — and it uses no property of the reading whatever. -/
theorem sum_over_labels_eq_sum_over_orbit
    (hAct : Function.Bijective (fun g : G => g • base)) (f : Lab → ℚ_[3]) :
    ∑ l : Lab, f l = ∑ g : G, f (g • base) :=
  (Fintype.sum_bijective (fun g : G => g • base) hAct (fun g => f (g • base)) f
    (fun _ => rfl)).symm

/-- **The deliverable identity.** If the labels are the orbit — `g ↦ g • base` bijective — then the
`|F_l|`-indexed normalization and the `F_l^⋆`-average agree, for **every** reading, invariant or not: the
numerators agree by reindexing (`sum_over_labels_eq_sum_over_orbit`) and the denominators by
`card_eq_card_of_bijective`. Nothing about `f` is used, which is why the identity is a statement about the
indexings rather than about the reading. -/
theorem averageOverLabels_eq_averageOverOrbit
    (hAct : Function.Bijective (fun g : G => g • base)) (f : Lab → ℚ_[3]) :
    averageOverLabels f = averageOverOrbit G base f := by
  unfold averageOverLabels averageOverOrbit
  rw [sum_over_labels_eq_sum_over_orbit base hAct f, card_eq_card_of_bijective base hAct]

end Reindexing

/-! ## 4. The W5 result as a corollary: for an invariant reading, averaging is evaluation at `base` -/

section InvariantAverages

variable {G : Type*} [Group G] [Fintype G] {Lab : Type*} [MulAction G Lab]

/-- The number of group elements, cast to `ℚ_[3]`, is nonzero. This is the hypothesis the division needs;
it holds because a group is nonempty. -/
theorem card_cast_ne_zero : ((Fintype.card G : ℕ) : ℚ_[3]) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Fintype.card_ne_zero

/-- **Under invariance the orbit sum is the cardinality times the value at the base label**: every summand
`f (g • base)` equals `f base`, so the sum is `card G` copies of it. -/
theorem sum_orbit_eq_card_mul (base : Lab) {f : Lab → ℚ_[3]} (hInv : InvariantReading G f) :
    ∑ g : G, f (g • base) = (Fintype.card G : ℚ_[3]) * f base := by
  rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => hInv g base), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- **The orbit average of an invariant reading is the value at the base label** — the W5 statement
`average_eq_value_of_invariant`, with the base label in place of its label `1`. The hypothesis `hAct` is
*not* needed for this half: the orbit average is exact as soon as the reading is constant on the orbit,
whether or not the orbit exhausts the label set. This asymmetry with `coord_at_base` is the point of the
anti-degeneracy in §5. -/
theorem averageOverOrbit_eq_base_of_invariant (base : Lab) {f : Lab → ℚ_[3]}
    (hInv : InvariantReading G f) : averageOverOrbit G base f = f base := by
  rw [averageOverOrbit, sum_orbit_eq_card_mul base hInv,
    mul_div_cancel_left₀ _ (card_cast_ne_zero (G := G))]

end InvariantAverages

section Coordinate

variable {Lab : Type*} [Fintype Lab] {G : Type*} [Group G] [Fintype G] [MulAction G Lab]

/-- **The label average of an invariant reading is the value at the base label (item 4 of the task).** This
is the W5 result recovered as a corollary of `averageOverLabels_eq_averageOverOrbit`: reindexing turns the
label average into the orbit average, and invariance turns the orbit average into the value at `base`. The
identification "label `0` ↔ orbit `⟨F_l^⋆⟩`" does its work here: it is what allows the label `base` to be
read off the group average. -/
theorem coord_at_base (base : Lab) (hAct : Function.Bijective (fun g : G => g • base))
    {f : Lab → ℚ_[3]} (hInv : InvariantReading G f) : averageOverLabels f = f base := by
  rw [averageOverLabels_eq_averageOverOrbit base hAct f,
    averageOverOrbit_eq_base_of_invariant base hInv]

end Coordinate

/-! ## 5. Anti-degeneracy: labels that are not the orbit, with the two averages computed

The label set is `ZMod 3` (three labels) and the group is its unit group, which has two elements and acts by
multiplication. The units swap the labels `1` and `2` and fix `0`, so the orbit of the base label `0` is
`{0}`: the labels are *not* the orbit, `g ↦ g • 0` is not injective, and `hAct` fails. For the reading
`1, 2, 3` the label average is `(1 + 2 + 3) / 3 = 2` while the orbit average is `(1 + 1) / 2 = 1`; the two
numbers are computed below and separated by `2 ≠ 1`. -/

section AntiDegeneracy

/-- The toy label set of the anti-degeneracy: three labels, standing for `|F_l|`. -/
abbrev ToyLab : Type := ZMod 3

/-- The toy group of the anti-degeneracy: the two units of `ZMod 3`, standing for `F_l^⋆`, acting on the
labels by multiplication. -/
abbrev ToyGroup : Type := (ZMod 3)ˣ

/-- Three labels. -/
theorem toyLab_card : Fintype.card ToyLab = 3 := ZMod.card 3

/-- Two group elements. -/
theorem toyGroup_card : Fintype.card ToyGroup = 2 := by decide

/-- The base label is fixed by the whole group: `0` is absorbing for multiplication. This is why the orbit
of `0` is the single label `{0}`, and it is also why the orbit sum below is two copies of `f 0`. -/
theorem toy_smul_zero (u : ToyGroup) : u • (0 : ToyLab) = 0 := by simp

/-- The three labels, enumerated. -/
theorem toy_univ : (Finset.univ : Finset ToyLab) = {0, 1, 2} := by decide

/-- The labels are distinct; these three facts are what let the sums below be evaluated rather than left as
`Finset.sum` expressions. -/
theorem toy_zero_ne_one : (0 : ToyLab) ≠ 1 := by decide

theorem toy_zero_ne_two : (0 : ToyLab) ≠ 2 := by decide

theorem toy_one_ne_two : (1 : ToyLab) ≠ 2 := by decide

/-- **The concrete reading**: `1` at the label `0`, `2` at the label `1`, `3` at the label `2`. -/
def toyReading (x : ToyLab) : ℚ_[3] := if x = 0 then 1 else if x = 1 then 2 else 3

/-- The reading at the base label. -/
theorem toyReading_zero : toyReading 0 = 1 := by simp [toyReading]

theorem toyReading_one : toyReading 1 = 2 := by
  have h : (1 : ToyLab) ≠ 0 := toy_zero_ne_one.symm
  simp [toyReading, h]

theorem toyReading_two : toyReading 2 = 3 := by
  have h0 : (2 : ToyLab) ≠ 0 := toy_zero_ne_two.symm
  have h1 : (2 : ToyLab) ≠ 1 := toy_one_ne_two.symm
  simp [toyReading, h0, h1]

/-- **The label sum, computed**: `1 + 2 + 3 = 6`. The sum over the three labels is expanded along the
enumeration `toy_univ`, and the reading is evaluated at each label. -/
theorem toyReading_sum : ∑ x : ToyLab, toyReading x = 6 := by
  rw [toy_univ, Finset.sum_insert (by decide), Finset.sum_pair toy_one_ne_two, toyReading_zero,
    toyReading_one, toyReading_two]
  norm_num

/-- **The orbit sum, computed**: both group elements fix the base label `0`, so the sum is `f 0 + f 0 = 2`,
and the division by `card G = 2` returns `f 0 = 1`. -/
theorem toyOrbit_sum : ∑ u : ToyGroup, toyReading (u • (0 : ToyLab)) = 2 := by
  calc ∑ u : ToyGroup, toyReading (u • (0 : ToyLab))
      = ∑ _u : ToyGroup, toyReading (0 : ToyLab) :=
        Finset.sum_congr rfl (fun u _ => by rw [toy_smul_zero])
    _ = 2 := by
        rw [Finset.sum_const, Finset.card_univ, toyGroup_card, nsmul_eq_mul, toyReading_zero,
          mul_one]
        norm_num

/-- **The `|F_l|`-indexed normalization of the concrete reading is `2`**: `6 / 3`. -/
theorem averageOverLabels_toyReading :
    averageOverLabels (fun x : ToyLab => toyReading x) = 2 := by
  unfold averageOverLabels
  rw [toyReading_sum, toyLab_card]
  rw [div_eq_iff (by norm_num : ((3 : ℕ) : ℚ_[3]) ≠ 0)]
  norm_num

/-- **The `F_l^⋆`-average of the concrete reading is `1`**: `2 / 2`. -/
theorem averageOverOrbit_toyReading :
    averageOverOrbit ToyGroup (0 : ToyLab) toyReading = 1 := by
  unfold averageOverOrbit
  rw [toyOrbit_sum, toyGroup_card]
  rw [div_eq_iff (by norm_num : ((2 : ℕ) : ℚ_[3]) ≠ 0)]
  norm_num

/-- The orbit average is the value at the base label here — the orbit half of §4 survives without `hAct`,
because the base label is fixed. It is the label half that fails, which is the content of
`toy_averages_differ`. -/
theorem averageOverOrbit_eq_value_at_base :
    averageOverOrbit ToyGroup (0 : ToyLab) toyReading = toyReading 0 := by
  rw [averageOverOrbit_toyReading, toyReading_zero]

/-- **The hypothesis of the main theorem genuinely fails here**: `g ↦ g • 0` is not injective, so it is not
a bijection of the two-element group onto the three labels. Equivalently, `2 ≠ 3`. -/
theorem toy_not_bijective : ¬ Function.Bijective (fun u : ToyGroup => u • (0 : ToyLab)) := by
  intro h
  have hc := card_eq_card_of_bijective (G := ToyGroup) (base := (0 : ToyLab)) h
  rw [toyGroup_card, toyLab_card] at hc
  exact absurd hc (by norm_num)

/-- **The anti-degeneracy (item 5 of the task), as computed numbers**: without `hAct` the two
normalizations differ — the label average is `2`, the orbit average is `1`. A concrete `≠` between two
computed values, not a negated universal. -/
theorem toy_averages_differ :
    averageOverLabels (fun x : ToyLab => toyReading x) ≠
      averageOverOrbit ToyGroup (0 : ToyLab) toyReading := by
  rw [averageOverLabels_toyReading, averageOverOrbit_toyReading]
  norm_num

end AntiDegeneracy

end

end LabelNormalization

#print axioms LabelNormalization.averageOverLabels
#print axioms LabelNormalization.averageOverOrbit
#print axioms LabelNormalization.InvariantReading
#print axioms LabelNormalization.card_eq_card_of_bijective
#print axioms LabelNormalization.sum_over_labels_eq_sum_over_orbit
#print axioms LabelNormalization.averageOverLabels_eq_averageOverOrbit
#print axioms LabelNormalization.card_cast_ne_zero
#print axioms LabelNormalization.sum_orbit_eq_card_mul
#print axioms LabelNormalization.averageOverOrbit_eq_base_of_invariant
#print axioms LabelNormalization.coord_at_base
#print axioms LabelNormalization.ToyLab
#print axioms LabelNormalization.ToyGroup
#print axioms LabelNormalization.toyLab_card
#print axioms LabelNormalization.toyGroup_card
#print axioms LabelNormalization.toy_smul_zero
#print axioms LabelNormalization.toy_univ
#print axioms LabelNormalization.toy_zero_ne_one
#print axioms LabelNormalization.toy_zero_ne_two
#print axioms LabelNormalization.toy_one_ne_two
#print axioms LabelNormalization.toyReading
#print axioms LabelNormalization.toyReading_zero
#print axioms LabelNormalization.toyReading_one
#print axioms LabelNormalization.toyReading_two
#print axioms LabelNormalization.toyReading_sum
#print axioms LabelNormalization.toyOrbit_sum
#print axioms LabelNormalization.averageOverLabels_toyReading
#print axioms LabelNormalization.averageOverOrbit_toyReading
#print axioms LabelNormalization.averageOverOrbit_eq_value_at_base
#print axioms LabelNormalization.toy_not_bijective
#print axioms LabelNormalization.toy_averages_differ
