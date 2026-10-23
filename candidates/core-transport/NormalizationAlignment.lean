import CoreLog.QpThree

/-!
# W5 toy province: averaging over the label orbit equals evaluating at the label

**Scope.** This file formalises one algebraic identity and, separately, one concrete failure of it when
the hypothesis is dropped. The setting is a finite group `G` acting on itself, respectively on a finite
label set `X`, and the values are in `ℚ_[3]`. Nothing else is formalised: no topology, no logarithm
series, no structure beyond `Fintype`, `Group` and `MulAction`.

**Why this obligation exists.** `research/core-backward-2026-10-23/h3-prerequisites.md`, §对齐义务, records
the source alignment that has to be given a shape. IUT II, Corollary 4.10, (i) (txt 7003–7010) *identifies*
the collections of data `Ψcns(F)_0` and `Ψcns(F)_{⟨F_l^⋆⟩}` "via the isomorphism of the second display of
Corollary 4.6, (iii)". IUT III, Step (x) (txt 10904–10922), says the procession-normalized mono-analytic
log-volumes are those "where the average is taken over `j ∈ F_l^⋆`". The reading quoted in (xi-d)
(txt 11022) is indexed instead by `j ∈ |F_l|`, the label set. So the source averages over a *group*
`F_l^⋆` in one place and indexes by a *label set* `|F_l|` in another, with the label `0` standing for
`⟨F_l^⋆⟩`.

**The content of that identification, as formalised here.** The two indexings give the same number as soon
as the reading being averaged is invariant under the label action: invariance makes the summand constant on
the orbit, and the average of a constant over a set of size `n`, divided by `n`, is that constant. That is
the whole algebraic content of "the average over the orbit is the value at the label", and it is what
`average_eq_value_of_invariant` (item 3 of the task) and its special case `alignment` (item 4) state. The
label-set version (`InvariantOn`, `orbit_sum_eq_card_mul`, `orbitAverageOn`, `orbitAverageOn_eq_value`)
states the same thing when the group acts on a separate label set rather than on itself, which is the
shape the source's `j ∈ F_l^⋆` versus `j ∈ |F_l|` comparison actually has.

**What is proved.** In order:
* `Invariant`, `orbitAverage` — the hypothesis and the average over the orbit, both over `ℚ_[3]`.
* `sum_mul_left`, `orbitAverage_mul_left` — the left-regular action reindexes the sum: `∑ g, f (a * g)`
  equals `∑ g, f g` for every `a`. This is the step that makes the average an average *over the orbit*, and
  it needs no invariance at all.
* `sum_eq_card_mul` — under `Invariant`, the sum is `card G` times the value at the label `1`.
* `average_eq_value_of_invariant` — `orbitAverage f = f g` for **every** label `g`; `alignment` is the case
  `g = 1`: the average over the orbit is the value at the label.
* `invariant_iff_const` — on a group acting on itself by left multiplication, invariance is *equivalent to
  constancy. This is stated rather than left implicit, because it is where the strength (and the limit) of
  the toy lies; see the non-claims below.
* `invariant_const`, `orbitAverage_const` — non-vacuity: the hypothesis of the main theorem is satisfiable,
  and for a constant reading the average is that constant, so the weights do sum to one.
* `orbit_sum_eq_card_mul`, `orbitAverageOn_eq_value` — the label-set version, stated for an arbitrary
  `MulAction G X` (no `Fintype X`, no transitivity).
* **Anti-degeneracy (item 5)**: the label group `LabelGroup := Equiv.Perm (Fin 2)`, i.e. the symmetric
  group on two labels, with the concrete reading `nonInvariantReading` taking the value `5` at `1` and `7`
  at the transposition `swapLabels`. Then `orbitAverage_nonInvariantReading` computes the average to be
  `6 = 12 / 2`, `nonInvariantReading_one` gives the value at the label as `5`, and
  `orbitAverage_ne_value` separates them: `6 ≠ 5`. This is a concrete `≠` between two computed numbers,
  not a negated universal, and `nonInvariantReading_not_invariant` shows the hypothesis of the main
  theorem genuinely fails for that reading.

**What this file does not say.** It is a toy, and the following are outside it.
1. It does **not** show that (xi-d) uses the procession convention. Whether the `|F_l|` index of (xi-d) is
   the same convention as the `F_l^⋆` average of Step (x) is a *definition alignment* in the source
   (h3-prerequisites.md, item 1 of 要补的证明), supported by IUT II Corollary 4.10, (i) and by IUT III
   txt 10917–10922. Here only the algebraic implication "invariant reading ⇒ average equals value" is
   established, for an abstract finite group. The identification itself is not proved, and is not a
   theorem of this file.
2. No procession, capsule, theta value, theta-link, `F_l^⋆`, `|F_l|`, `⟨F_l^⋆⟩`, F-prime-strip,
   Frobenioid, log-volume, log-shell, Hodge theater, coricity, poly-isomorphism, `Ism` or `Ind1`/`Ind2`/
   `Ind3` occurs in this file. `LabelGroup` is `Equiv.Perm (Fin 2)`, a two-element toy group, not the label
   group of a number field; its elements are permutations of `Fin 2`, not capsules of a procession.
3. It says nothing about `ℚ_[3]` beyond its commutative field structure: the norm, the valuation and the
   logarithm series that the W1–W4 provinces use do not occur here. The choice of `ℚ_[3]` only fixes a
   concrete field in which the two averages of the anti-degeneracy can be *computed*.
4. It is not evidence for or against any IUT claim. The core GAP of
   `research/core-backward-2026-10-23/h3-prerequisites.md` stays OPEN: the `M`-uniqueness (M-i, M-ii) and
   the two unwritten normalizations (M-iii) are untouched.
5. The hypothesis `Invariant` is strong, and `invariant_iff_const` says exactly how strong: for a group
   acting on itself by left multiplication it forces the reading to be constant, so
   `average_eq_value_of_invariant` is not a serious averaging theorem on that carrier — it is the
   statement that "constant on the orbit" collapses the average. That is the intended reading (the
   source's claim is precisely that the reading does not depend on the label representative), but the
   theorem must not be quoted as though it showed something about non-constant readings.
   `orbitAverageOn_eq_value` is the form in which the orbit can be a proper subset of the carrier, and
   even there the hypothesis forces constancy on the orbit itself, not merely on average.

**Why nothing is imported from the earlier provinces.** `ReadingInvariance.lean`,
`TransitionCompatibility.lean`, `CollectionProvenance.lean` and the other toy files are top-level modules
of the package: `lakefile.lean` declares a single library, `lean_lib CoreTransport`, whose modules are the
ones under `CoreTransport/`, so those files are not Lake targets, no `olean` of them exists, and
`import TransitionCompatibility` is not available. Nothing from them is needed here: this file's
mathematics is finite-group averaging, so there is nothing to restate, and the only import is
`CoreLog.QpThree`, which supplies the notation `ℚ_[3]` and Mathlib's `Padic` field structure.

A dependency-footprint block at the end of the file records, for every declaration below, that the only
dependencies are `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace NormalizationAlignment

noncomputable section

/-! ## 1. The reading, the label action on the group itself, and the orbit average -/

section General

variable {G : Type*} [Group G] [Fintype G]

/-- **The reading is invariant under the label action.** `G` acts on itself on the left (`b ↦ a * b`); this
says the reading `f` gives the same value at `a * b` as at `b`, i.e. it does not see which representative
of the label orbit is used. This is the hypothesis of `average_eq_value_of_invariant` and `alignment`, and
`nonInvariantReading_not_invariant` below exhibits a reading for which it fails. -/
def Invariant (f : G → ℚ_[3]) : Prop := ∀ a b : G, f (a * b) = f b

/-- **The orbit average**: the sum of the reading over the whole label orbit (here: over `G`), divided by
the number of labels. Division is by the cardinality of `G`, cast to `ℚ_[3]`; that cast is nonzero by
`card_cast_ne_zero`. This is the toy stand-in for "the average is taken over `j ∈ F_l^⋆`". -/
def orbitAverage (f : G → ℚ_[3]) : ℚ_[3] :=
  (∑ g : G, f g) / (Fintype.card G : ℚ_[3])

/-- The number of labels is not zero. A group is nonempty, so its `Fintype` cardinality is positive; this
is the hypothesis the division in `orbitAverage` needs, in the form stated by the task. -/
theorem card_ne_zero : Fintype.card G ≠ 0 := Fintype.card_ne_zero

/-- The same fact after the cast to `ℚ_[3]`, which is the form `mul_div_cancel_left₀` consumes. -/
theorem card_cast_ne_zero : ((Fintype.card G : ℕ) : ℚ_[3]) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Fintype.card_ne_zero

omit [Fintype G] in
/-- **Invariance pins the reading to its value at the label `1`.** From `f (g * 1) = f 1`. Note that
`Fintype` is not used, hence the `omit`. -/
theorem invariant_apply_eq_one {f : G → ℚ_[3]} (hf : Invariant f) (g : G) : f g = f 1 := by
  simpa using hf g 1

omit [Fintype G] in
/-- **On this carrier, invariance is constancy, and conversely.** This is not a defect of the toy to be
hidden: for the group acting on itself by left multiplication, "does not depend on the label
representative" means "constant", which is exactly what the source's identification of the `0` label with
the whole orbit `⟨F_l^⋆⟩` amounts to at the level of indexings. The label-set version
(`orbitAverageOn_eq_value`) is where the carrier is larger than the orbit. `Invariant f` holds exactly
when `f` is constant, with value `f 1`. -/
theorem invariant_iff_const {f : G → ℚ_[3]} : Invariant f ↔ ∀ g : G, f g = f 1 := by
  constructor
  · intro hf g
    exact invariant_apply_eq_one hf g
  · intro h a b
    rw [h (a * b), h b]

/-- **The average is an average over the orbit.** Left multiplication by `a` is a bijection of the label
set, so summing the reading against the permuted labels does not change the sum. This is the step that
uses the left-regular action, and it does **not** use `Invariant`: the sum over a permuted orbit is the
same sum, whatever the reading is. -/
theorem sum_mul_left (f : G → ℚ_[3]) (a : G) : ∑ g : G, f (a * g) = ∑ g : G, f g := by
  refine Fintype.sum_bijective (fun g : G => a * g) ⟨?_, ?_⟩ (fun g => f (a * g)) f
    (fun g => rfl)
  · intro x y h
    exact mul_left_cancel h
  · intro b
    refine ⟨a⁻¹ * b, ?_⟩
    show a * (a⁻¹ * b) = b
    exact mul_inv_cancel_left a b

/-- Consequently the orbit average is itself unchanged when the reading is composed with the label action.
Nothing here needs the reading to be invariant. -/
theorem orbitAverage_mul_left (f : G → ℚ_[3]) (a : G) :
    orbitAverage (fun g => f (a * g)) = orbitAverage f := by
  show (∑ g : G, f (a * g)) / (Fintype.card G : ℚ_[3])
      = (∑ g : G, f g) / (Fintype.card G : ℚ_[3])
  rw [sum_mul_left f a]

/-- **Under invariance the sum is the cardinality times the value at the label.** Every summand is `f 1`
(`invariant_apply_eq_one`), so the sum is `card G` copies of it. -/
theorem sum_eq_card_mul {f : G → ℚ_[3]} (hf : Invariant f) :
    ∑ g : G, f g = (Fintype.card G : ℚ_[3]) * f 1 := by
  have hconst : ∀ g : G, f g = f 1 := fun g => invariant_apply_eq_one hf g
  rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => hconst g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- **The alignment (item 3 of the task).** For a reading invariant under the label action, the average
over the orbit equals the value at *any* label `g`, not merely at `1`: the average is `card G` copies of
`f 1`, divided by `card G`, and `f g = f 1` by invariance. The division cancels because the number of
labels is nonzero (`card_cast_ne_zero`). -/
theorem average_eq_value_of_invariant {f : G → ℚ_[3]} (hf : Invariant f) (g : G) :
    orbitAverage f = f g := by
  have hg : f g = f 1 := invariant_apply_eq_one hf g
  rw [orbitAverage, sum_eq_card_mul hf, hg,
    mul_div_cancel_left₀ _ (card_cast_ne_zero (G := G))]

/-- **The alignment, in the form the source's identification uses (item 4 of the task):** the average over
the orbit is the value at the label `1`. This is the special case `g = 1` of
`average_eq_value_of_invariant`, and it is the exact algebraic content of "the label `0` stands for the
group `⟨F_l^⋆⟩`": indexing by the group and indexing by the label give the same number. -/
theorem alignment {f : G → ℚ_[3]} (hf : Invariant f) : orbitAverage f = f 1 :=
  average_eq_value_of_invariant hf 1

omit [Fintype G] in
/-- A constant reading is invariant, so the hypothesis of the main theorem is satisfiable: the file is not
vacuous. -/
theorem invariant_const (c : ℚ_[3]) : Invariant (fun _ : G => c) := fun _ _ => rfl

/-- **The weights sum to one**: the orbit average of a constant reading is that constant. This is
`alignment` applied to `invariant_const`, and it is what makes the division in `orbitAverage` a genuine
average rather than an arbitrary normalization. -/
theorem orbitAverage_const (c : ℚ_[3]) : orbitAverage (fun _ : G => c) = c :=
  alignment (invariant_const c)

end General

/-! ## 2. The label-set form: a group acting on a set of labels

The source averages over `j ∈ F_l^⋆` (a group) but (xi-d) indexes by `j ∈ |F_l|` (a label set). The
section below states the same identity for a reading on an arbitrary label set `X` with `G` acting on it,
which is the shape that comparison has. No `Fintype X` is needed, and transitivity of the action is not
needed: the sum runs over the acting group, so each orbit point is counted with multiplicity the size of
its stabilizer. That multiplicity is harmless precisely because the summand is constant (`hφ`). -/

section LabelAction

variable {G : Type*} [Group G] [Fintype G] {X : Type*} [MulAction G X]

/-- **`G`-invariance of a reading on the label set.** The group argument is explicit because `G` does not
otherwise occur in the type of `φ`. -/
def InvariantOn (G : Type*) [Group G] {X : Type*} [MulAction G X] (φ : X → ℚ_[3]) : Prop :=
  ∀ (a : G) (x : X), φ (a • x) = φ x

/-- **The sum over the acting group is the cardinality times the value at the label.** This is the
label-set analogue of `sum_eq_card_mul`, and it is the sense in which "averaging over `j ∈ F_l^⋆`" and
"the value at the label" are the same number: the sum over the group is the constant value repeated once
per group element, regardless of how the orbit sits inside `X`. -/
theorem orbit_sum_eq_card_mul {φ : X → ℚ_[3]} (hφ : InvariantOn G φ) (x : X) :
    (∑ a : G, φ (a • x)) = (Fintype.card G : ℚ_[3]) * φ x := by
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hφ a x), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- **The orbit average at a label**, for a reading on a label set: the sum of the reading over the images
`a • x` of the label `x`, divided by the number of group elements. -/
def orbitAverageOn (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (φ : X → ℚ_[3]) (x : X) : ℚ_[3] :=
  (∑ a : G, φ (a • x)) / (Fintype.card G : ℚ_[3])

/-- **The label-set form of the alignment.** For a reading on the label set invariant under the label
action, the average over the orbit of a label equals the reading at that label. The orbit may be a proper
subset of `X` here, so this is the form in which the averaging has non-trivial content; what invariance
forces is constancy on the orbit, and that is exactly what the source's identification uses. -/
theorem orbitAverageOn_eq_value {φ : X → ℚ_[3]} (hφ : InvariantOn G φ) (x : X) :
    orbitAverageOn G φ x = φ x := by
  have hcard : ((Fintype.card G : ℕ) : ℚ_[3]) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [orbitAverageOn, orbit_sum_eq_card_mul hφ x, mul_div_cancel_left₀ _ hcard]

end LabelAction

/-! ## 3. The concrete label group: two labels, and the group that permutes them

`LabelGroup := Equiv.Perm (Fin 2)` is the smallest non-trivial label group: `Fin 2` is a two-element label
set and `LabelGroup` is its symmetric group, of order two. This is the toy stand-in for `F_l^⋆`; its two
elements are the identity `1` and the transposition `swapLabels`, which is the analogue of the label `0`
versus the orbit `⟨F_l^⋆⟩` of the source's identification. -/

/-- The toy label group: the permutations of a two-element label set. -/
abbrev LabelGroup := Equiv.Perm (Fin 2)

/-- The non-identity label permutation: `0 ↦ 1 ↦ 0`. This is the element that stands for "the other
representative of the orbit". -/
def swapLabels : LabelGroup := Equiv.swap 0 1

/-- A two-element `Fin` is `0` or `1`. -/
theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- The two elements of the toy label group are distinct: `1 ≠ swapLabels`. -/
theorem one_ne_swap : (1 : LabelGroup) ≠ swapLabels := by
  intro h
  have h0 : swapLabels (0 : Fin 2) = 1 := by
    show Equiv.swap (0 : Fin 2) 1 0 = 1
    exact Equiv.swap_apply_left 0 1
  rw [← h] at h0
  have hone : (1 : LabelGroup) (0 : Fin 2) = 0 := rfl
  rw [hone] at h0
  exact absurd h0 (by decide)

/-- **The toy label group has exactly two elements**, `1` and `swapLabels`: a permutation of `Fin 2` is
determined by where it sends `0`, and there are only two possibilities. -/
theorem eq_one_or_swap (σ : LabelGroup) : σ = 1 ∨ σ = swapLabels := by
  by_cases h : σ 0 = 0
  · left
    have h1 : σ 1 = 1 := by
      rcases fin_two_eq_zero_or_one (σ 1) with hz | ho
      · exfalso
        have hinj : (1 : Fin 2) = 0 := σ.injective (by rw [hz, h])
        exact absurd hinj (by decide)
      · exact ho
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · simpa using h
    · simpa using h1
  · right
    have h0 : σ 0 = 1 := by
      rcases fin_two_eq_zero_or_one (σ 0) with hz | ho
      · exact absurd hz h
      · exact ho
    have h1 : σ 1 = 0 := by
      rcases fin_two_eq_zero_or_one (σ 1) with hz | ho
      · exact hz
      · exfalso
        have hinj : (0 : Fin 2) = 1 := σ.injective (by rw [ho, h0])
        exact absurd hinj (by decide)
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · show σ 0 = Equiv.swap (0 : Fin 2) 1 0
      rw [h0, Equiv.swap_apply_left]
    · show σ 1 = Equiv.swap (0 : Fin 2) 1 1
      rw [h1, Equiv.swap_apply_right]

/-- The label group's underlying set is the two-element set `{1, swapLabels}`. No cardinality computation
is used: the inclusion `univ ⊆ {1, swapLabels}` comes from `eq_one_or_swap`, and the reverse inclusion is
`Finset.subset_univ`. -/
theorem univ_eq : (Finset.univ : Finset LabelGroup) = {1, swapLabels} := by
  refine Finset.Subset.antisymm ?_ (Finset.subset_univ _)
  intro σ _
  rcases eq_one_or_swap σ with h | h
  · rw [h]
    exact Finset.mem_insert_self _ _
  · rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The number of labels is two, read off from `univ_eq` rather than from `Nat.factorial`. -/
theorem card_eq : Fintype.card LabelGroup = 2 := by
  rw [← Finset.card_univ, univ_eq, Finset.card_pair one_ne_swap]

/-- **The orbit average on the toy label group, computed**: it is the arithmetic mean of the reading at the
two elements. This is what makes the anti-degeneracy below a computation rather than an assertion. -/
theorem orbitAverage_perm_two (f : LabelGroup → ℚ_[3]) :
    orbitAverage f = (f 1 + f swapLabels) / 2 := by
  rw [orbitAverage, univ_eq, Finset.sum_pair one_ne_swap, card_eq]
  norm_num

/-! ## 4. Anti-degeneracy: a reading that is not invariant, and whose average is not its value

The reading below takes the value `5` at the identity label and `7` at the transposition. Its orbit average
is `(5 + 7) / 2 = 6`, while its value at the label `1` is `5`; the two are separated by `6 ≠ 5`. So the
hypothesis of `alignment` is not automatic: drop it, and averaging over the orbit gives a number different
from evaluating at the label. This is the concrete `≠` required, at explicit values. -/

/-- **A non-invariant reading on the toy label group**: `5` at the identity label, `7` at the transposition
label. -/
def nonInvariantReading (σ : LabelGroup) : ℚ_[3] := if σ = 1 then 5 else 7

/-- The reading at the identity label is `5`. -/
theorem nonInvariantReading_one : nonInvariantReading 1 = 5 := by
  simp [nonInvariantReading]

/-- The reading at the transposition label is `7`. -/
theorem nonInvariantReading_swap : nonInvariantReading swapLabels = 7 := by
  have h : swapLabels ≠ (1 : LabelGroup) := one_ne_swap.symm
  simp [nonInvariantReading, h]

/-- **The concrete reading is not invariant.** At `(swapLabels, 1)` invariance would read
`nonInvariantReading swapLabels = nonInvariantReading 1`, i.e. `7 = 5`. -/
theorem nonInvariantReading_not_invariant : ¬ Invariant nonInvariantReading := by
  intro hf
  have h : (7 : ℚ_[3]) = 5 := by
    have hh := hf swapLabels 1
    rwa [mul_one, nonInvariantReading_swap, nonInvariantReading_one] at hh
  exact absurd h (by norm_num)

/-- **The orbit average of the concrete reading is `6`**: `(5 + 7) / 2`. -/
theorem orbitAverage_nonInvariantReading : orbitAverage nonInvariantReading = 6 := by
  rw [orbitAverage_perm_two, nonInvariantReading_one, nonInvariantReading_swap]
  norm_num

/-- **The anti-degeneracy statement of the file (item 5 of the task), as a computed inequality**: the
average over the orbit is `6`, the value at the label is `5`, and `6 ≠ 5`. A concrete witness, not a
negated universal. -/
theorem orbitAverage_ne_value : orbitAverage nonInvariantReading ≠ nonInvariantReading 1 := by
  rw [orbitAverage_nonInvariantReading, nonInvariantReading_one]
  norm_num

end

end NormalizationAlignment

#print axioms NormalizationAlignment.Invariant
#print axioms NormalizationAlignment.orbitAverage
#print axioms NormalizationAlignment.card_ne_zero
#print axioms NormalizationAlignment.card_cast_ne_zero
#print axioms NormalizationAlignment.invariant_apply_eq_one
#print axioms NormalizationAlignment.invariant_iff_const
#print axioms NormalizationAlignment.sum_mul_left
#print axioms NormalizationAlignment.orbitAverage_mul_left
#print axioms NormalizationAlignment.sum_eq_card_mul
#print axioms NormalizationAlignment.average_eq_value_of_invariant
#print axioms NormalizationAlignment.alignment
#print axioms NormalizationAlignment.invariant_const
#print axioms NormalizationAlignment.orbitAverage_const
#print axioms NormalizationAlignment.InvariantOn
#print axioms NormalizationAlignment.orbit_sum_eq_card_mul
#print axioms NormalizationAlignment.orbitAverageOn
#print axioms NormalizationAlignment.orbitAverageOn_eq_value
#print axioms NormalizationAlignment.LabelGroup
#print axioms NormalizationAlignment.swapLabels
#print axioms NormalizationAlignment.fin_two_eq_zero_or_one
#print axioms NormalizationAlignment.one_ne_swap
#print axioms NormalizationAlignment.eq_one_or_swap
#print axioms NormalizationAlignment.univ_eq
#print axioms NormalizationAlignment.card_eq
#print axioms NormalizationAlignment.orbitAverage_perm_two
#print axioms NormalizationAlignment.nonInvariantReading
#print axioms NormalizationAlignment.nonInvariantReading_one
#print axioms NormalizationAlignment.nonInvariantReading_swap
#print axioms NormalizationAlignment.nonInvariantReading_not_invariant
#print axioms NormalizationAlignment.orbitAverage_nonInvariantReading
#print axioms NormalizationAlignment.orbitAverage_ne_value
