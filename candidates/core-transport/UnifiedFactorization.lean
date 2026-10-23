import CoreLog.QpThree

/-!
# W7: one descent lemma for both provinces — a reading constant on a join of relations, and two instances

**Scope.** This file proves one general statement about a type `α` carrying **two** relations and a reading
`f : α → ℚ_[3]`, together with the two instances that make it a unification of W5 and W6, and it exhibits
concrete failures of each hypothesis. It is a toy province: not a fact-tree entry, not a registry entry, not
an audit of any IUT object. The core GAP of `research/core-backward-2026-10-23/` stays OPEN.

**The obligation, in one sentence.** `research/core-backward-2026-10-23/h1-coricity.md` records that the
source determines `n,◦HT^{D-Θ±ellNF}` only "up to isomorphism" (txt 8869–8873 via Theorem 1.5(i),
2881–2889) and that a poly-isomorphism is an **orbit of isomorphisms** (txt 2005–2007); the invariance
therefore has to hold *on the classes of an equivalence relation*, not on a chosen presentation. That is the
difference between "constant on a chain of presentations" (a comparison of values indexed by `Fin k`) and
"the reading is a function on the quotient" (a pullback of a function on the classes), and it is why the
obligation is stated as a **descent**.

**Two earlier provinces, and what this file adds.**

* W5 (`candidates/core-transport/NormalizationAlignment.lean`) proved, for a reading on a group carrier
  invariant under the label action, that the orbit average equals the value at the label
  (`average_eq_value_of_invariant`, `alignment`): invariance makes the summand constant on the orbit, so the
  average collapses onto the value. Its hypothesis is exactly "constant on the steps of the orbit relation".
* W6 (`candidates/core-transport/ReadingFactorization.lean`) built `SameObject` as the reflexive–transitive
  closure of the transport relation and `descendedReading` by `Quotient.lift`, with
  `descendedReading_mk`: the reading is constant on `SameObject`, hence descends.

Both are the same theorem: **a reading constant on the steps of two relations is constant on the relation
their union generates, and therefore descends to the quotient by it.** The join of the two relations is
`Join R S := Relation.ReflTransGen (fun x y => R x y ∨ S x y)`, the reflexive–transitive closure of the
union; the common special case is `R = Eq` (W5: the base case is equality, the content is the orbit) or
`S = Eq` (W6: the content is the transports, equality is the trivial step). The general statement below
covers both at once and does not have to know which of the two relations carries the content.

**What is proved, in order.**

1. `constant_of_join` — if `f` is constant on `R`-steps and on `S`-steps then it is constant along
   `Relation.ReflTransGen (R ∪ S)`, by induction on the closure (item 1 of the task).
2. `join_refl`, `join_symm`, `join_trans`, `join_equivalence`, `joinedSetoid` — the join of two equivalence
   relations is an equivalence relation, packaged as a `Setoid` (item 2). `join_refl` needs no hypothesis;
   symmetry and transitivity reuse the symmetry and transitivity of `R` and of `S` step by step.
3. `descended` — `Quotient.lift` of `f` along the joined setoid, with the obligation discharged by
   `constant_of_join` (item 3). `descended_mk` is the computation rule (item 4), and `descended_unique`
   shows the descent is the only function on the quotient that computes `f` — the statement W6
   (`descendedReading_unique`) had and which has no chain-level analogue.
4. `join_imp_right`, `join_imp_left` — if one relation is contained in the other, the join is the bigger
   one. These are the lemmas that make each instance *reduce* to the general theorem rather than merely
   resemble it: with `R = Eq` the join is the orbit relation, with `S = Eq` the join is the transports.
5. **Instance (a), W5's shape** (`orbitRel`, `labelOrbit`, `sumReading`, `w5Descended`, …): the carrier is
   the label vectors `Fin 2 → ℚ_[3]`, the group is `LabelGroup := Equiv.Perm (Fin 2)` permuting the two
   labels, `S` is the orbit relation of that action and `R` is equality. The reading is the sum of the
   entries, which is constant on the orbit (`sumReading_of_orbit`), so `descended` applies and
   `w5Descended ⟦v⟧ = sumReading v`. On the two-element orbit `{vecOne, vecSwap}` this recovers W5's
   conclusion — the value at a label and the average over the orbit are the same number
   (`w5_average_eq_value`) — and `classes_distinct` shows the quotient of instance (a) is **not** a
   subsingleton, so this is not a degenerate descent.
6. **Instance (b), W6's shape** (`TransportStep`, `ChainRel`, `relativeInput`, `w6Descended`, …): the
   carrier is `Fin 3`, the transport data are the presentations `chainInput i = 4 ^ (i+1)` and the
   comparison units `chainUnit i j = 4 ^ (j - i)`; `R` is the reflexive–transitive closure of the one-step
   relation "the recorded transition carries the presentation at `a` to the one at `b`", and `S` is
   equality. `relativeInput` is the presentation at `i` transported back to the base frame — W6's
   `relativeInput` with the logarithm left off, since the reading here is the transported presentation
   itself. `relativeInput_eq_of_rel` is the constancy obligation, proved **per step** from the cocycle
   identity (`relativeInput_eq_of_step`), and `join_eq_chainRel` records that equality adds nothing to the
   join, i.e. that the joined relation *is* W6's `SameObject`.
7. **Anti-degeneracy, both sides, with explicit numbers.** `diffReading v = v 0 - v 1` is `-1` at `vecOne`
   and `1` at `vecSwap`, which are in the same orbit: so the `S`-constancy hypothesis of item 1 fails, and
   `no_factorization_when_S_constancy_fails` proves that **no** function on the joined quotient computes
   `diffReading`. On the transport side, `brokenUnit` records the comparison transition `0 → 2` as
   `4 ^ 3 = 64` instead of `4 ^ 2 = 16` (W6's `chainBroken`), so `brokenNoStep_02` rules out the one-step
   relation while `brokenRel_02` still relates `0` and `2` in two steps, and the readings there are `4` at
   `0` and `1` at `2`: `brokenReading_not_constant` states that the `R`-constancy hypothesis fails, and
   `no_factorization_on_broken` that no function on the quotient computes those readings. Each file of the
   task's item 6 alternatives is thus exhibited, and in both cases the *equivalence* hypotheses still hold:
   what fails is the constancy of the reading, which is the point.
8. One dependency-footprint line per declaration, at the end of the file.

**Restated, not imported.** Neither W5 nor W6 is importable: `lakefile.lean` declares a single library
`CoreTransport` whose modules are those under `CoreTransport/`, so `NormalizationAlignment.lean` and
`ReadingFactorization.lean`, being top-level modules of the package, are not Lake targets, no `olean` of
them exists, and `import` of either is unavailable. Everything used from them is therefore restated here,
with the same statements and the same numbers: from W5, the label group `Equiv.Perm (Fin 2)`, the
transposition `Equiv.swap 0 1`, the invariance hypothesis (`Invariant`, here `sumReading_of_orbit`), and the
two-element average `(f 1 + f swapLabels) / 2` of the non-invariant reading; from W6, the one-step transport
relation defined from `input * unit = input'`, its reflexive–transitive closure, the per-step constancy
argument, the cocycle law and the broken chain whose comparison transition is `4 ^ 3` rather than `4 ^ 2`.
Two things are *not* restated: W6's logarithm series (`CoreTransport.localLog` and its convergence), because
the reading in this file is an arbitrary function `α → ℚ_[3]` whose constancy is the hypothesis and not a
theorem, and W5's `orbitAverage` with its division by `Fintype.card`, because only the two-element orbit
occurs here and its average is written out (`w5_average_eq_value`). The single import is `CoreLog.QpThree`,
which supplies `ℚ_[3]`.

**Non-claims.** (1) This does not say that the IUT object carries two such relations, nor that any reading
of the real object is presentation-independent: it is a statement about an abstract type with two relations.
(2) Nothing about procession, capsules, theta values, Θ-links, `F_l^⋆`, `|F_l|`, F-prime-strips,
Frobenioids, log-volumes, log-shells, Hodge theaters, coricity, poly-isomorphisms, `Ism`, `Ind1`/`Ind2`/
`Ind3`, `M`, `N_E`, packet normalization or `det^{⊗M}` occurs. `LabelGroup` is `Equiv.Perm (Fin 2)`; `Fin 3`
is a set of indices, not the set of places of a number field; the transports are multiplication by powers of
`4` on `ℚ_[3]`. (3) `ℚ_[3]` is used only as a commutative field: no norm, no valuation, no logarithm.
(4) The unification is *formal*: it identifies the shape of the two obligations (constancy on the generated
relation, descent to its quotient), not their mathematical content; in particular it does not upgrade W5's
averaging into a theorem about non-constant readings, and on the label-vector carrier where the action is
transitive an `S`-constant reading is constant on each orbit by construction. (5) It is not evidence for or
against any IUT claim.

A dependency-footprint block at the end records, for every declaration below, that the only dependencies are
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace UnifiedFactorization

noncomputable section

/-! ## 1. The join of two relations, and constancy along it -/

/-- **The join of two relations**: the reflexive–transitive closure of their union. It is the relation
"finitely many steps, each of them an `R`-step or an `S`-step", and it is what both provinces are secretly
about: W5's orbit relation is the join of equality with the group action's steps, W6's `SameObject` is the
join of the transport steps with equality. No hypothesis is built into the definition: the equivalence
laws are proved in `join_equivalence` and are hypotheses of `joinedSetoid`, not of `Join` itself. -/
def Join {α : Type*} (R S : α → α → Prop) : α → α → Prop :=
  Relation.ReflTransGen (fun x y => R x y ∨ S x y)

/-- A single `R`-step is a join-step. -/
theorem join_incl_left {α : Type*} {R S : α → α → Prop} {a b : α} (h : R a b) : Join R S a b :=
  Relation.ReflTransGen.single (Or.inl h)

/-- A single `S`-step is a join-step. -/
theorem join_incl_right {α : Type*} {R S : α → α → Prop} {a b : α} (h : S a b) : Join R S a b :=
  Relation.ReflTransGen.single (Or.inr h)

/-- **Item 1 of the task: constancy on both relations gives constancy on their join.** The proof is the
induction on the reflexive–transitive closure that the statement asks for: the reflexive case is `rfl`, and
each step of the closure is discharged by `hR` or by `hS` according to which side of the union it is. Note
that neither relation has to be an equivalence relation for this step; the equivalence hypotheses enter only
with the quotient, in `joinedSetoid`. -/
theorem constant_of_join {α : Type*} {R S : α → α → Prop} {f : α → ℚ_[3]}
    (hR : ∀ a b, R a b → f a = f b) (hS : ∀ a b, S a b → f a = f b) :
    ∀ a b, Relation.ReflTransGen (fun x y => R x y ∨ S x y) a b → f a = f b := by
  intro a b h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      exact ih.trans (by
        rcases hbc with h | h
        · exact hR _ _ h
        · exact hS _ _ h)

/-- The join is reflexive, with no hypothesis on `R` or `S`. -/
theorem join_refl {α : Type*} {R S : α → α → Prop} (a : α) : Join R S a a :=
  Relation.ReflTransGen.refl

/-- **The join is symmetric as soon as `R` and `S` are**, one step at a time. This is where the two
equivalence hypotheses are consumed for the first time; the relation is *not* symmetric on its own (a
closure of a symmetric relation is symmetric, but the closure of a non-symmetric one need not be). -/
theorem join_symm {α : Type*} {R S : α → α → Prop} (hR : Equivalence R) (hS : Equivalence S)
    {a b : α} (h : Join R S a b) : Join R S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head (by
        rcases hbc with h | h
        · exact Or.inl (hR.symm h)
        · exact Or.inr (hS.symm h)) ih

/-- The join is transitive: the closure is closed under composition, with no hypothesis on `R` or `S`. -/
theorem join_trans {α : Type*} {R S : α → α → Prop} {a b c : α} (hab : Join R S a b)
    (hbc : Join R S b c) : Join R S a c :=
  Relation.ReflTransGen.trans hab hbc

/-- **The join of two equivalence relations is an equivalence relation.** Reflexivity and transitivity are
structural; symmetry is `join_symm` and uses `hR`, `hS` once per step. -/
theorem join_equivalence {α : Type*} {R S : α → α → Prop} (hR : Equivalence R) (hS : Equivalence S) :
    Equivalence (Join R S) where
  refl := fun a => join_refl a
  symm := fun h => join_symm hR hS h
  trans := fun h1 h2 => join_trans h1 h2

/-- **Item 2 of the task: the joined setoid.** Its relation is `Join R S`, and its equivalence field is
`join_equivalence`, so the quotient below is the quotient by the *join* of the two relations and not by some
refinement of it. -/
def joinedSetoid {α : Type*} (R S : α → α → Prop) (hR : Equivalence R) (hS : Equivalence S) :
    Setoid α :=
  Setoid.mk (Join R S) (join_equivalence hR hS)

/-- The setoid's relation *is* `Join R S`, definitionally: packaging the join into a `Setoid` changes
nothing, so `descended` really is the lift along the join. -/
theorem joinedSetoid_rfl {α : Type*} (R S : α → α → Prop) (hR : Equivalence R) (hS : Equivalence S) :
    (joinedSetoid R S hR hS).r = Join R S := rfl

/-- **Item 3 of the task: the descended reading.** `Quotient.lift` of `f` along the joined setoid, with the
obligation `Join R S a b → f a = f b` discharged by `constant_of_join`. The two constancy hypotheses are
kept as explicit arguments (rather than derived) because they are exactly the two hypotheses of the two
provinces: `hRc` is W6's constancy along the transports, `hSc` is W5's invariance. -/
def descended {α : Type*} (R S : α → α → Prop) (hR : Equivalence R) (hS : Equivalence S)
    (f : α → ℚ_[3]) (hRc : ∀ a b, R a b → f a = f b) (hSc : ∀ a b, S a b → f a = f b) :
    Quotient (joinedSetoid R S hR hS) → ℚ_[3] :=
  Quotient.lift f (fun a b hab => constant_of_join hRc hSc a b hab)

/-- **Item 4 of the task: the computation rule of the descent.** The descended function on the class of `a`
is the reading at `a`; this is `Quotient.lift_mk` and holds definitionally. -/
theorem descended_mk {α : Type*} (R S : α → α → Prop) (hR : Equivalence R) (hS : Equivalence S)
    (f : α → ℚ_[3]) (hRc : ∀ a b, R a b → f a = f b) (hSc : ∀ a b, S a b → f a = f b) (a : α) :
    descended R S hR hS f hRc hSc (Quotient.mk (joinedSetoid R S hR hS) a) = f a := rfl

/-- **The descent is unique**: any function on the joined quotient that computes the reading agrees with
`descended`. This is the sense in which "descends to the quotient" is stronger than "constant on the
relation": it produces a function *on the classes*, and only one such function can compute the reading. -/
theorem descended_unique {α : Type*} (R S : α → α → Prop) (hR : Equivalence R) (hS : Equivalence S)
    (f : α → ℚ_[3]) (hRc : ∀ a b, R a b → f a = f b) (hSc : ∀ a b, S a b → f a = f b)
    (g : Quotient (joinedSetoid R S hR hS) → ℚ_[3])
    (hg : ∀ a : α, g (Quotient.mk (joinedSetoid R S hR hS) a) = f a) :
    g = descended R S hR hS f hRc hSc := by
  funext q
  refine Quotient.ind (motive := fun q => g q = descended R S hR hS f hRc hSc q) (fun a => ?_) q
  rw [hg a, descended_mk]

/-- **If `R` is contained in `S`, the join adds nothing to `S`.** This is the lemma by which instance (a)
reduces to the general theorem: with `R = Eq` the join of equality with the orbit relation *is* the orbit
relation, so the descent of `descended` is the descent along the orbit alone. -/
theorem join_imp_right {α : Type*} {R S : α → α → Prop} (hS : Equivalence S)
    (hRS : ∀ a b, R a b → S a b) {a b : α} (h : Join R S a b) : S a b := by
  induction h with
  | refl => exact hS.refl a
  | tail _ hbc ih =>
      exact hS.trans ih (by
        rcases hbc with h | h
        · exact hRS _ _ h
        · exact h)

/-- **If `S` is contained in `R`, the join adds nothing to `R`.** This is the lemma by which instance (b)
reduces to the general theorem: with `S = Eq` the join of the transport relation with equality *is* the
transport relation, i.e. W6's `SameObject`, so the descent of `descended` is W6's `descendedReading`. -/
theorem join_imp_left {α : Type*} {R S : α → α → Prop} (hR : Equivalence R)
    (hSR : ∀ a b, S a b → R a b) {a b : α} (h : Join R S a b) : R a b := by
  induction h with
  | refl => exact hR.refl a
  | tail _ hbc ih =>
      exact hR.trans ih (by
        rcases hbc with h | h
        · exact h
        · exact hSR _ _ h)

/-! ## 2. The orbit relation of a group action

Both provinces have a group in them: W5's carrier is acted on by `F_l^⋆` (here `Equiv.Perm (Fin 2)`), and
W6's transports are the steps. The orbit relation of an action is the second relation of the general
statement, so it is defined and proved to be an equivalence relation once, for an arbitrary `MulAction`. -/

/-- **The orbit relation of a group action**: `a` and `b` are related when some group element carries `a`
to `b`. The group and the carrier are explicit arguments because neither is determined by the relation
alone; this is the same device W5 used for `InvariantOn`. -/
def orbitRel (G : Type*) [Group G] (X : Type*) [MulAction G X] (a b : X) : Prop :=
  ∃ g : G, g • a = b

/-- **The orbit relation is an equivalence relation.** Reflexivity is the unit of the group, symmetry is the
inverse, transitivity is the product — so the `S`-side hypothesis `hS` of the general statement is
discharged by the group law alone. -/
theorem orbitRel_equivalence (G : Type*) [Group G] (X : Type*) [MulAction G X] :
    Equivalence (orbitRel G X) where
  refl := fun a => ⟨1, one_smul G a⟩
  symm := fun h => by
    rcases h with ⟨g, hg⟩
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  trans := fun h1 h2 => by
    rcases h1 with ⟨g, hg⟩
    rcases h2 with ⟨h, hh⟩
    exact ⟨h * g, by rw [mul_smul, hg, hh]⟩

/-! ## 3. Instance (a): the orbit relation of the label action, with equality as the base case — W5

The carrier is the set of label vectors `Fin 2 → ℚ_[3]`, the group is `Equiv.Perm (Fin 2)` permuting the two
labels, and the reading is the sum of the entries. `S` is the orbit relation of the action and `R` is
equality: this is W5's configuration with the group action written out, and the descent below is the general
`descended` specialised to it.

Mathlib has no instance making `Equiv.Perm (Fin 2)` act on `Fin 2 → ℚ_[3]` (the action is not the pointwise
one), so the action is installed here; `labelVector_smul_apply` records its computation rule, and every
subsequent use goes through that rule rather than through unfolding. -/

/-- The toy label group of W5: the permutations of a two-element label set. -/
abbrev LabelGroup := Equiv.Perm (Fin 2)

/-- The carrier of instance (a): a value in `ℚ_[3]` attached to each of the two labels. -/
abbrev LabelVector := Fin 2 → ℚ_[3]

/-- **The label action**: `g` sends the vector `v` to `i ↦ v (g⁻¹ i)`, i.e. it permutes the labels. The two
laws are definitional for this action. -/
instance labelVectorMulAction : MulAction LabelGroup LabelVector where
  smul g v := fun i => v (g.symm i)
  one_smul v := by funext i; rfl
  mul_smul g h v := by funext i; rfl

/-- The computation rule of the label action, at each label. -/
theorem labelVector_smul_apply (g : LabelGroup) (v : LabelVector) (i : Fin 2) :
    (g • v) i = v (g.symm i) := rfl

/-- The non-identity label permutation, W5's `swapLabels`: `0 ↦ 1 ↦ 0`. -/
def swapLabels : LabelGroup := Equiv.swap 0 1

/-- The transposition is its own inverse, which is why `labelVector_smul_apply` computes cleanly at it. -/
theorem swapLabels_symm : swapLabels.symm = swapLabels := rfl

/-- The transposition sends the label `0` to the label `1`. -/
theorem swapLabels_zero : swapLabels (0 : Fin 2) = 1 := Equiv.swap_apply_left 0 1

/-- The transposition sends the label `1` to the label `0`. -/
theorem swapLabels_one : swapLabels (1 : Fin 2) = 0 := Equiv.swap_apply_right 0 1

/-- The orbit relation of the label action: the `S` of instance (a). -/
abbrev labelOrbit : LabelVector → LabelVector → Prop := orbitRel LabelGroup LabelVector

/-- The orbit relation of the label action is an equivalence relation, by `orbitRel_equivalence`. -/
theorem labelOrbit_equivalence : Equivalence labelOrbit :=
  orbitRel_equivalence LabelGroup LabelVector

/-- **The reading of instance (a)**: the sum over the labels. It is the toy stand-in for a reading that does
not depend on which representative of the labelling orbit is used — W5's `Invariant`, read on vectors. -/
def sumReading (v : LabelVector) : ℚ_[3] := ∑ i, v i

/-- **The reading is unchanged by relabelling**: the sum over a permuted index set is the same sum. This is
W5's `sum_mul_left` in the shape the general statement needs. -/
theorem sumReading_smul (g : LabelGroup) (v : LabelVector) : sumReading (g • v) = sumReading v := by
  show (∑ i, v (g.symm i)) = ∑ i, v i
  exact Equiv.sum_comp g.symm v

/-- **The `S`-constancy hypothesis of instance (a)**: `sumReading` is constant on orbit steps. This is
exactly W5's hypothesis (`Invariant`) transported to the general statement's shape, and it is stated as a
function of both indices so that it can be passed directly as the hypothesis `hSc` of `descended`. -/
theorem sumReading_of_orbit : ∀ v w : LabelVector, labelOrbit v w → sumReading v = sumReading w := by
  intro v w h
  rcases h with ⟨g, rfl⟩
  exact (sumReading_smul g v).symm

/-- The first of the two concrete label vectors: the entry at the label `i` is `i + 1`, i.e. `(1, 2)`. -/
def vecOne : LabelVector := fun i => (i.val : ℚ_[3]) + 1

/-- The second concrete vector: the entry at the label `i` is `2 - i`, i.e. `(2, 1)` — `vecOne` with the
labels exchanged. -/
def vecSwap : LabelVector := fun i => 2 - (i.val : ℚ_[3])

/-- A vector in a **different** orbit: the entry at the label `i` is `4 * i + 1`, i.e. `(1, 5)`, whose sum is
`6` rather than `3`. -/
def vecOther : LabelVector := fun i => 4 * (i.val : ℚ_[3]) + 1

/-- **The two vectors are in the same orbit**: the transposition carries `(1, 2)` to `(2, 1)`. Both sides are
computed at the two labels, so the orbit membership is a computation and not an assumption. -/
theorem swap_smul_vecOne : swapLabels • vecOne = vecSwap := by
  funext i
  rw [labelVector_smul_apply]
  fin_cases i
  · simp only [swapLabels, vecOne, vecSwap, Equiv.symm_swap]
    norm_num
  · simp only [swapLabels, vecOne, vecSwap, Equiv.symm_swap]
    norm_num

/-- The orbit membership, as an `S`-step. -/
theorem orbit_vecOne_vecSwap : labelOrbit vecOne vecSwap := ⟨swapLabels, swap_smul_vecOne⟩

/-- The reading at the first vector is `3`. -/
theorem sumReading_vecOne : sumReading vecOne = 3 := by
  rw [sumReading, Fin.sum_univ_two]
  norm_num [vecOne]

/-- The reading at the second vector is also `3`: it is the same orbit. -/
theorem sumReading_vecSwap : sumReading vecSwap = 3 := by
  rw [sumReading, Fin.sum_univ_two]
  norm_num [vecSwap]

/-- The reading at the vector of the other orbit is `6`. -/
theorem sumReading_vecOther : sumReading vecOther = 6 := by
  rw [sumReading, Fin.sum_univ_two]
  norm_num [vecOther]

/-- **Instance (a)'s descent**: `R` is equality, `S` is the label orbit, and `descended` applies with
`hRc` the trivial constancy of a function on equal arguments and `hSc` the orbit invariance. This is the
general theorem, not a re-proof: the body is `descended` at these arguments. -/
def w5Descended :
    Quotient (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) → ℚ_[3] :=
  descended Eq labelOrbit eq_equivalence labelOrbit_equivalence sumReading
    (fun _ _ h => congrArg sumReading h) sumReading_of_orbit

/-- The computation rule of instance (a)'s descent: it computes the reading. -/
theorem w5Descended_mk (v : LabelVector) :
    w5Descended (Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) v)
      = sumReading v :=
  descended_mk Eq labelOrbit eq_equivalence labelOrbit_equivalence sumReading
    (fun _ _ h => congrArg sumReading h) sumReading_of_orbit v

/-- **The descended function at the class of `vecOne` is `3`.** -/
theorem w5Descended_vecOne :
    w5Descended (Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecOne)
      = 3 := by
  rw [w5Descended_mk, sumReading_vecOne]

/-- **The descended function at the class of `vecSwap` is `3`** — the same orbit, the same value, and the
two classes are equal by `Quotient.sound`. -/
theorem w5Descended_vecSwap :
    w5Descended (Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecSwap)
      = 3 := by
  rw [w5Descended_mk, sumReading_vecSwap]

/-- **W5's conclusion recovered as a corollary**: on the two-element orbit the average of the reading over
the orbit is the value at the label. W5 proved this as `alignment` for `orbitAverage`; here it is the
arithmetic content of that statement at the concrete orbit `{vecOne, vecSwap}`, on top of the descent. -/
theorem w5_average_eq_value : (sumReading vecOne + sumReading vecSwap) / 2 = sumReading vecOne := by
  rw [sumReading_vecOne, sumReading_vecSwap]
  rw [div_eq_iff (by norm_num : (2 : ℚ_[3]) ≠ 0)]
  norm_num

/-- **The quotient of instance (a) is not a subsingleton**, unlike W6's chains: two vectors in different
orbits have different descended values, hence different classes. This is why instance (a) is a genuine
instance and not a collapse. -/
theorem classes_distinct :
    Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecOne
      ≠ Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecOther := by
  intro h
  have h1 : sumReading vecOne = sumReading vecOther := by
    rw [← w5Descended_mk vecOne, ← w5Descended_mk vecOther, h]
  rw [sumReading_vecOne, sumReading_vecOther] at h1
  norm_num at h1

/-- **The join of equality with the orbit relation is the orbit relation**: `join_imp_right` at instance
(a)'s data. So the general statement's `Join` really is the orbit relation here, and the descent of §3 is
the descent along the orbit. -/
theorem join_eq_labelOrbit {v w : LabelVector} (h : Join Eq labelOrbit v w) : labelOrbit v w :=
  join_imp_right labelOrbit_equivalence
    (fun a b hab => by rw [← hab]; exact ⟨1, one_smul LabelGroup a⟩) h

/-! ## 4. Instance (b): the transport-generated relation, with equality as the trivial step — W6

The carrier is `Fin 3` (three presentations of one object), the transports are multiplication by powers of
`4` on `ℚ_[3]`, `R` is the reflexive–transitive closure of the one-step relation "the recorded transition
carries the presentation at `a` to the presentation at `b`", and `S` is equality. The reading is the
presentation at `i` transported back to the base frame, `chainInput i / chainUnit 0 i`; W6's reading was the
`p`-adic logarithm of that quotient, whose constancy it proved separately, and the logarithm is left out
here because the constancy of the reading is this file's hypothesis (`hRc`) and not its conclusion. -/

/-- The presentation at each index: `4 ^ (i + 1)`, i.e. the chain `4, 16, 64` of W4/W6. -/
def chainInput (i : Fin 3) : ℚ_[3] := (4 : ℚ_[3]) ^ (i.val + 1)

/-- **The compatible comparison unit** from `i` to `j`: `4 ^ (j - i)`. It satisfies the cocycle law
(`chainUnit_cocycle`), which is what makes the elementary transports agree with the comparison ones. -/
def chainUnit (i j : Fin 3) : ℚ_[3] := (4 : ℚ_[3]) ^ (j.val - i.val)

/-- **The broken comparison unit**: W6's `expBroken`, `d + d / 2` with `d = j - i`. It agrees with
`chainUnit` on the elementary pairs (`0 → 1`, `1 → 2`, and the diagonal) but records `4 ^ 3 = 64` instead of
`4 ^ 2 = 16` for `0 → 2`. -/
def brokenUnit (i j : Fin 3) : ℚ_[3] := (4 : ℚ_[3]) ^ (j.val - i.val + (j.val - i.val) / 2)

/-- **The one-step transport relation**: the recorded transition from `a` to `b` really carries the
presentation at `a` to the presentation at `b`. Both orientations are recorded, as in W6, because the unit is
indexed by ordered pairs; the order hypothesis is carried along so that the cocycle law can be applied in
its orientation, but it plays no role in the definition itself. The relation is defined from the transport
data only and never mentions a reading, which is what makes the constancy obligations below real. -/
def TransportStep (unit : Fin 3 → Fin 3 → ℚ_[3]) (a b : Fin 3) : Prop :=
  (∃ _ : a.val ≤ b.val, chainInput a * unit a b = chainInput b) ∨
    (∃ _ : b.val ≤ a.val, chainInput b * unit b a = chainInput a)

/-- **`ChainRel unit`: the transport-generated relation**, the reflexive–transitive closure of the one-step
relation. This is W6's `SameObject`. It is *not* an equivalence relation by construction — the closure of a
relation giving both orientations happens to be one, and `chainRel_equivalence` proves it. -/
def ChainRel (unit : Fin 3 → Fin 3 → ℚ_[3]) (a b : Fin 3) : Prop :=
  Relation.ReflTransGen (TransportStep unit) a b

/-- **The transported presentation at `i`**, relative to the base index `0`: the presentation at `i`
multiplied by the inverse of the comparison unit. This is W6's `Chain.relativeInput`. -/
def relativeInput (unit : Fin 3 → Fin 3 → ℚ_[3]) (i : Fin 3) : ℚ_[3] :=
  chainInput i / unit 0 i

/-- The comparison unit at the base index is a power of `4`. -/
theorem chainUnit_zero (j : Fin 3) : chainUnit 0 j = (4 : ℚ_[3]) ^ j.val := by
  simp [chainUnit]

/-- **The cocycle law** for the compatible units: `unit 0 b = unit 0 a * unit a b` for `a ≤ b`. This is the
identity that makes the transported presentation independent of the intermediate presentation, and it is the
only place where arithmetic about exponents is used. It is stated as a function of both indices so that it
can be passed directly as the hypothesis `hcoc` of `relativeInput_eq_of_step`. -/
theorem chainUnit_cocycle :
    ∀ a b : Fin 3, a.val ≤ b.val → chainUnit 0 b = chainUnit 0 a * chainUnit a b := by
  intro a b h
  rw [chainUnit_zero, chainUnit_zero]
  show (4 : ℚ_[3]) ^ b.val = (4 : ℚ_[3]) ^ a.val * (4 : ℚ_[3]) ^ (b.val - a.val)
  rw [← pow_add, Nat.add_sub_cancel' h]

/-- Every compatible comparison unit is nonzero: it is a power of `4`. -/
theorem chainUnit_ne_zero (a b : Fin 3) : chainUnit a b ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- Every broken comparison unit is nonzero: it is a power of `4`. -/
theorem brokenUnit_ne_zero (a b : Fin 3) : brokenUnit a b ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- **One correct transport preserves the transported presentation.** If the transition `a → b` carries the
presentation at `a` to the one at `b`, and the units satisfy the cocycle law, then the two base-frame
transports coincide. The proof cancels the nonzero comparison unit `unit 0 b`, which is the per-step content
of W6's `reading_eq_of_transport` with the logarithm removed. -/
theorem relativeInput_eq_of_step {unit : Fin 3 → Fin 3 → ℚ_[3]}
    (hcoc : ∀ a b : Fin 3, a.val ≤ b.val → unit 0 b = unit 0 a * unit a b)
    (hne : ∀ a b : Fin 3, unit a b ≠ 0)
    {a b : Fin 3} (h : a.val ≤ b.val) (hstep : chainInput a * unit a b = chainInput b) :
    relativeInput unit a = relativeInput unit b := by
  have hb : unit 0 b = unit 0 a * unit a b := hcoc a b h
  refine mul_right_cancel₀ (hne 0 b) ?_
  calc relativeInput unit a * unit 0 b
      = chainInput a / unit 0 a * (unit 0 a * unit a b) := by simp only [relativeInput, hb]
    _ = chainInput a / unit 0 a * unit 0 a * unit a b := by rw [mul_assoc]
    _ = chainInput a * unit a b := by rw [div_mul_cancel₀ _ (hne 0 a)]
    _ = chainInput b := hstep
    _ = chainInput b / unit 0 b * unit 0 b := by rw [div_mul_cancel₀ _ (hne 0 b)]
    _ = relativeInput unit b * unit 0 b := by simp only [relativeInput]

/-- **The `R`-constancy hypothesis of instance (b)**: the reading is constant along the transport-generated
relation, proved by induction on the closure and per step by `relativeInput_eq_of_step` — not by appealing to
a global `reading_compatible`. This is W6's `sameObject_reading_eq`, and it is the `hRc` argument of the
general theorem. -/
theorem relativeInput_eq_of_rel {unit : Fin 3 → Fin 3 → ℚ_[3]}
    (hcoc : ∀ a b : Fin 3, a.val ≤ b.val → unit 0 b = unit 0 a * unit a b)
    (hne : ∀ a b : Fin 3, unit a b ≠ 0) :
    ∀ a b : Fin 3, ChainRel unit a b → relativeInput unit a = relativeInput unit b := by
  intro a b h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rcases hbc with ⟨hb, hstep⟩ | ⟨hb, hstep⟩
      · exact ih.trans (relativeInput_eq_of_step hcoc hne hb hstep)
      · exact ih.trans (relativeInput_eq_of_step hcoc hne hb hstep).symm

/-- The one-step relation is symmetric, since both orientations are recorded. -/
theorem transportStep_symm {unit : Fin 3 → Fin 3 → ℚ_[3]} {a b : Fin 3}
    (h : TransportStep unit a b) : TransportStep unit b a := h.symm

/-- **The closure of a symmetric relation is symmetric.** Proved by induction on the closure, because
Mathlib's `Relation.ReflTransGen` API does not carry a symmetry lemma; the same proof is in W6
(`reflTransGen_symm`), restated here. -/
theorem reflTransGen_symm {α : Type*} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih

/-- `ChainRel` is symmetric. -/
theorem chainRel_symm {unit : Fin 3 → Fin 3 → ℚ_[3]} {a b : Fin 3} (h : ChainRel unit a b) :
    ChainRel unit b a :=
  reflTransGen_symm (fun _ _ => transportStep_symm) h

/-- **`ChainRel` is an equivalence relation**: reflexivity and transitivity are structural, symmetry is
`chainRel_symm`. This discharges the `hR` hypothesis of the general statement for instance (b). -/
theorem chainRel_equivalence (unit : Fin 3 → Fin 3 → ℚ_[3]) : Equivalence (ChainRel unit) where
  refl := fun _ => Relation.ReflTransGen.refl
  symm := fun h => chainRel_symm h
  trans := fun h1 h2 => Relation.ReflTransGen.trans h1 h2

/-- The presentation at the base index is `4`. -/
theorem chainInput_zero : chainInput 0 = (4 : ℚ_[3]) := by
  norm_num [chainInput]

/-- The presentation at the index `2` is `64`. -/
theorem chainInput_two : chainInput 2 = (64 : ℚ_[3]) := by
  norm_num [chainInput]

/-- **The comparison transition `0 → 2` of the compatible chain transports the presentation**:
`4 * 4 ^ 2 = 4 ^ 3`, i.e. `4 * 16 = 64`. So `0` and `2` are related in **one** step there, which is W6's
`chainCompat_transport_02`. -/
theorem chainStep_02 : TransportStep chainUnit 0 2 :=
  Or.inl ⟨by decide, by norm_num [chainInput, chainUnit]⟩

/-- The transported presentation at the base index is `4`. -/
theorem relativeInput_chainUnit_zero : relativeInput chainUnit 0 = 4 := by
  norm_num [relativeInput, chainUnit, chainInput]

/-- **The transported presentation at `2` is the same `4`**: the compatible chain transports `64` back to
`4` by the comparison unit `16`. The value is obtained from the per-step lemma rather than by a division,
so the arithmetic is the same arithmetic the constancy obligation uses. -/
theorem relativeInput_chainUnit_two : relativeInput chainUnit 2 = 4 := by
  have h := relativeInput_eq_of_step chainUnit_cocycle chainUnit_ne_zero (a := 0) (b := 2)
    (by decide) (by norm_num [chainInput, chainUnit])
  rw [relativeInput_chainUnit_zero] at h
  exact h.symm

/-- **Instance (b)'s descent**: `R` is the transport-generated relation, `S` is equality, and the body is the
general theorem's `descended`. So W6's `descendedReading` is an instance of `descended`. -/
def w6Descended :
    Quotient
      (joinedSetoid (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence) →
        ℚ_[3] :=
  descended (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence
    (relativeInput chainUnit) (relativeInput_eq_of_rel chainUnit_cocycle chainUnit_ne_zero)
    (fun _ _ h => congrArg (relativeInput chainUnit) h)

/-- The computation rule of instance (b)'s descent. -/
theorem w6Descended_mk (i : Fin 3) :
    w6Descended
        (Quotient.mk
          (joinedSetoid (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence) i)
      = relativeInput chainUnit i :=
  descended_mk (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence
    (relativeInput chainUnit) (relativeInput_eq_of_rel chainUnit_cocycle chainUnit_ne_zero)
    (fun _ _ h => congrArg (relativeInput chainUnit) h) i

/-- **The descended reading of instance (b) at the base presentation is `4`.** -/
theorem w6Descended_zero :
    w6Descended
        (Quotient.mk
          (joinedSetoid (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence) 0)
      = 4 := by
  rw [w6Descended_mk, relativeInput_chainUnit_zero]

/-- **The descended reading at `2` is also `4`**: the value at the base presentation represents the whole
class, which is W6's `descendedReading_const` read at the other presentation. -/
theorem w6Descended_two :
    w6Descended
        (Quotient.mk
          (joinedSetoid (ChainRel chainUnit) Eq (chainRel_equivalence chainUnit) eq_equivalence) 2)
      = 4 := by
  rw [w6Descended_mk, relativeInput_chainUnit_two]

/-- **The join of the transport relation with equality is the transport relation**: `join_imp_left` at
instance (b)'s data. So the general statement's `Join` really *is* W6's `SameObject` here, and equality
contributes nothing — the second relation of the general statement is allowed to be trivial. -/
theorem join_eq_chainRel {a b : Fin 3} (h : Join (ChainRel chainUnit) Eq a b) :
    ChainRel chainUnit a b :=
  join_imp_left (chainRel_equivalence chainUnit)
    (fun a b hab => by rw [← hab]; exact Relation.ReflTransGen.refl) h

/-! ## 5. Anti-degeneracy, `S` side: a reading that is not constant on the orbit

The reading `diffReading v = v 0 - v 1` takes the value `-1` at `vecOne` and `1` at `vecSwap`, which are in
the same orbit. So the hypothesis `hSc` of `constant_of_join` fails, and there is no function on the joined
quotient that computes `diffReading` — the explicit numbers `-1` and `1` are the witness. The *equivalence*
hypothesis on `S` still holds (`labelOrbit_equivalence`): what fails is the constancy of the reading, which
is the point of the example. -/

/-- **A reading that is not constant on the label orbit**: the difference of the two entries. It is
antisymmetric under exchanging the labels, so it separates two vectors of one orbit. -/
def diffReading (v : LabelVector) : ℚ_[3] := v 0 - v 1

/-- The antisymmetric reading at `(1, 2)` is `-1`. -/
theorem diffReading_vecOne : diffReading vecOne = -1 := by
  norm_num [diffReading, vecOne]

/-- The antisymmetric reading at `(2, 1)` is `1`. -/
theorem diffReading_vecSwap : diffReading vecSwap = 1 := by
  norm_num [diffReading, vecSwap]

/-- **The `S`-constancy hypothesis genuinely fails for `diffReading`**: the two vectors are in the same
orbit, and the readings are `-1` and `1`. -/
theorem diffReading_not_constant :
    ¬ (∀ v w : LabelVector, labelOrbit v w → diffReading v = diffReading w) := by
  intro hc
  have h := hc vecOne vecSwap orbit_vecOne_vecSwap
  rw [diffReading_vecOne, diffReading_vecSwap] at h
  norm_num at h

/-- **No factorization through the joined quotient exists when the `S`-constancy hypothesis fails.** The
obligation of `Quotient.lift` is not a technicality here: `vecOne` and `vecSwap` are joined (they are related
by an `S`-step), so any function on the quotient would have to give them the same value, while the reading
gives `-1` and `1`. The failing hypothesis is named: `hSc`, the constancy of the reading on `S`-steps. -/
theorem no_factorization_when_S_constancy_fails :
    ¬ ∃ fBar : Quotient (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) → ℚ_[3],
        ∀ v : LabelVector,
          fBar (Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) v)
            = diffReading v := by
  rintro ⟨fBar, hf⟩
  have hq :
      Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecOne =
        Quotient.mk (joinedSetoid Eq labelOrbit eq_equivalence labelOrbit_equivalence) vecSwap :=
    Quotient.sound (join_incl_right orbit_vecOne_vecSwap)
  have h : diffReading vecOne = diffReading vecSwap := by
    rw [← hf vecOne, ← hf vecSwap, hq]
  rw [diffReading_vecOne, diffReading_vecSwap] at h
  norm_num at h

/-! ## 6. Anti-degeneracy, `R` side: the broken chain, where the transport constancy fails

This is W6's `chainBroken`: the same presentations `4, 16, 64` and the same elementary transitions, but the
comparison transition `0 → 2` is recorded as `4 ^ 3 = 64` instead of `4 ^ 2 = 16`. Then `4 * 64 = 256 ≠ 64`,
so there is no one-step relation between `0` and `2`; the elementary steps are untouched, so `0` and `2` are
still related in two steps, and the readings there are `4` at `0` and `1` at `2`. Hence the hypothesis `hRc`
of `constant_of_join` fails on the broken chain, and no function on its joined quotient computes the
readings. -/

/-- The broken elementary transition `0 → 1` is correct: `4 * 4 = 16`. -/
theorem brokenStep_01 : TransportStep brokenUnit 0 1 :=
  Or.inl ⟨by decide, by norm_num [chainInput, brokenUnit]⟩

/-- The broken elementary transition `1 → 2` is correct: `16 * 4 = 64`. -/
theorem brokenStep_12 : TransportStep brokenUnit 1 2 :=
  Or.inl ⟨by decide, by norm_num [chainInput, brokenUnit]⟩

/-- **The one-step relation is strictly smaller on the broken chain**: the recorded comparison transition
`0 → 2` is `4 ^ 3 = 64`, so `4 * 64 = 256 ≠ 64` and no one-step relation joins `0` to `2`. Explicit
numbers, as in W6's `chainBroken_no_direct_edge`. -/
theorem brokenNoStep_02 : ¬ TransportStep brokenUnit 0 2 := by
  rintro (⟨-, he⟩ | ⟨-, he⟩) <;> norm_num [chainInput, brokenUnit] at he

/-- **`0` and `2` are still related on the broken chain**, but in two steps, through the elementary
transitions `0 → 1 → 2`. The closure restores the pair that the defective comparison transition lost, which
is exactly why the defect has to be detected by the reading and not by the relation. -/
theorem brokenRel_02 : ChainRel brokenUnit 0 2 :=
  Relation.ReflTransGen.head brokenStep_01 (Relation.ReflTransGen.single brokenStep_12)

/-- The transported presentation at `0` of the broken chain is `4`. -/
theorem relativeInput_broken_zero : relativeInput brokenUnit 0 = 4 := by
  norm_num [relativeInput, brokenUnit, chainInput]

/-- The transported presentation at `1` of the broken chain is `4`: the comparison unit `0 → 1` is the
correct `4`. -/
theorem relativeInput_broken_one : relativeInput brokenUnit 1 = 4 := by
  have h1 : chainInput 1 = (16 : ℚ_[3]) := by norm_num [chainInput]
  have hu : brokenUnit 0 1 = (4 : ℚ_[3]) := by norm_num [brokenUnit]
  rw [relativeInput, h1, hu, div_eq_iff (by norm_num : (4 : ℚ_[3]) ≠ 0)]
  norm_num

/-- **The transported presentation at `2` of the broken chain is `1`**: the recorded transition `0 → 2` is
`64`, which cancels the presentation `64` there. In W6 the corresponding reading was
`localLog 1 = 0`; here it is the transported presentation `1` itself. -/
theorem relativeInput_broken_two : relativeInput brokenUnit 2 = 1 := by
  have h2 : chainInput 2 = (64 : ℚ_[3]) := by norm_num [chainInput]
  have hu : brokenUnit 0 2 = (64 : ℚ_[3]) := by norm_num [brokenUnit]
  rw [relativeInput, h2, hu, div_self (by norm_num : (64 : ℚ_[3]) ≠ 0)]

/-- **The `R`-constancy hypothesis genuinely fails on the broken chain**: `1` and `2` are joined by an
elementary transport, and the transported presentations there are `4` and `1`. This is W6's
`constancy_not_universal_on_broken`, with the two readings as explicit numbers rather than as logarithms. -/
theorem brokenReading_not_constant :
    ¬ (∀ a b : Fin 3, ChainRel brokenUnit a b →
        relativeInput brokenUnit a = relativeInput brokenUnit b) := by
  intro hc
  have h := hc 1 2 (Relation.ReflTransGen.single brokenStep_12)
  rw [relativeInput_broken_one, relativeInput_broken_two] at h
  norm_num at h

/-- **No factorization through the joined quotient exists on the broken chain.** This is W6's
`no_factorization_on_broken`, stated for the general statement's quotient: `1` and `2` are related, so any
function on the quotient would give the same value there, while the readings are `4` and `1`. The failing
hypothesis is `hRc`, the constancy of the reading on `R`-steps; the equivalence hypothesis on `R`
(`chainRel_equivalence`) still holds. -/
theorem no_factorization_on_broken :
    ¬ ∃ fBar : Quotient
          (joinedSetoid (ChainRel brokenUnit) Eq (chainRel_equivalence brokenUnit) eq_equivalence) →
            ℚ_[3],
        ∀ i : Fin 3,
          fBar
              (Quotient.mk
                (joinedSetoid (ChainRel brokenUnit) Eq (chainRel_equivalence brokenUnit)
                  eq_equivalence) i)
            = relativeInput brokenUnit i := by
  rintro ⟨fBar, hf⟩
  have hq :
      Quotient.mk
          (joinedSetoid (ChainRel brokenUnit) Eq (chainRel_equivalence brokenUnit) eq_equivalence) 1 =
        Quotient.mk
          (joinedSetoid (ChainRel brokenUnit) Eq (chainRel_equivalence brokenUnit) eq_equivalence) 2 :=
    Quotient.sound (join_incl_left (Relation.ReflTransGen.single brokenStep_12))
  have h : relativeInput brokenUnit 1 = relativeInput brokenUnit 2 := by
    rw [← hf 1, ← hf 2, hq]
  rw [relativeInput_broken_one, relativeInput_broken_two] at h
  norm_num at h

end

end UnifiedFactorization

#print axioms UnifiedFactorization.Join
#print axioms UnifiedFactorization.join_incl_left
#print axioms UnifiedFactorization.join_incl_right
#print axioms UnifiedFactorization.constant_of_join
#print axioms UnifiedFactorization.join_refl
#print axioms UnifiedFactorization.join_symm
#print axioms UnifiedFactorization.join_trans
#print axioms UnifiedFactorization.join_equivalence
#print axioms UnifiedFactorization.joinedSetoid
#print axioms UnifiedFactorization.joinedSetoid_rfl
#print axioms UnifiedFactorization.descended
#print axioms UnifiedFactorization.descended_mk
#print axioms UnifiedFactorization.descended_unique
#print axioms UnifiedFactorization.join_imp_right
#print axioms UnifiedFactorization.join_imp_left
#print axioms UnifiedFactorization.orbitRel
#print axioms UnifiedFactorization.orbitRel_equivalence
#print axioms UnifiedFactorization.LabelGroup
#print axioms UnifiedFactorization.LabelVector
#print axioms UnifiedFactorization.labelVectorMulAction
#print axioms UnifiedFactorization.labelVector_smul_apply
#print axioms UnifiedFactorization.swapLabels
#print axioms UnifiedFactorization.swapLabels_symm
#print axioms UnifiedFactorization.swapLabels_zero
#print axioms UnifiedFactorization.swapLabels_one
#print axioms UnifiedFactorization.labelOrbit
#print axioms UnifiedFactorization.labelOrbit_equivalence
#print axioms UnifiedFactorization.sumReading
#print axioms UnifiedFactorization.sumReading_smul
#print axioms UnifiedFactorization.sumReading_of_orbit
#print axioms UnifiedFactorization.vecOne
#print axioms UnifiedFactorization.vecSwap
#print axioms UnifiedFactorization.vecOther
#print axioms UnifiedFactorization.swap_smul_vecOne
#print axioms UnifiedFactorization.orbit_vecOne_vecSwap
#print axioms UnifiedFactorization.sumReading_vecOne
#print axioms UnifiedFactorization.sumReading_vecSwap
#print axioms UnifiedFactorization.sumReading_vecOther
#print axioms UnifiedFactorization.w5Descended
#print axioms UnifiedFactorization.w5Descended_mk
#print axioms UnifiedFactorization.w5Descended_vecOne
#print axioms UnifiedFactorization.w5Descended_vecSwap
#print axioms UnifiedFactorization.w5_average_eq_value
#print axioms UnifiedFactorization.classes_distinct
#print axioms UnifiedFactorization.join_eq_labelOrbit
#print axioms UnifiedFactorization.chainInput
#print axioms UnifiedFactorization.chainUnit
#print axioms UnifiedFactorization.brokenUnit
#print axioms UnifiedFactorization.TransportStep
#print axioms UnifiedFactorization.ChainRel
#print axioms UnifiedFactorization.relativeInput
#print axioms UnifiedFactorization.chainUnit_zero
#print axioms UnifiedFactorization.chainUnit_cocycle
#print axioms UnifiedFactorization.chainUnit_ne_zero
#print axioms UnifiedFactorization.brokenUnit_ne_zero
#print axioms UnifiedFactorization.relativeInput_eq_of_step
#print axioms UnifiedFactorization.relativeInput_eq_of_rel
#print axioms UnifiedFactorization.transportStep_symm
#print axioms UnifiedFactorization.reflTransGen_symm
#print axioms UnifiedFactorization.chainRel_symm
#print axioms UnifiedFactorization.chainRel_equivalence
#print axioms UnifiedFactorization.chainInput_zero
#print axioms UnifiedFactorization.chainInput_two
#print axioms UnifiedFactorization.chainStep_02
#print axioms UnifiedFactorization.relativeInput_chainUnit_zero
#print axioms UnifiedFactorization.relativeInput_chainUnit_two
#print axioms UnifiedFactorization.w6Descended
#print axioms UnifiedFactorization.w6Descended_mk
#print axioms UnifiedFactorization.w6Descended_zero
#print axioms UnifiedFactorization.w6Descended_two
#print axioms UnifiedFactorization.join_eq_chainRel
#print axioms UnifiedFactorization.diffReading
#print axioms UnifiedFactorization.diffReading_vecOne
#print axioms UnifiedFactorization.diffReading_vecSwap
#print axioms UnifiedFactorization.diffReading_not_constant
#print axioms UnifiedFactorization.no_factorization_when_S_constancy_fails
#print axioms UnifiedFactorization.brokenStep_01
#print axioms UnifiedFactorization.brokenStep_12
#print axioms UnifiedFactorization.brokenNoStep_02
#print axioms UnifiedFactorization.brokenRel_02
#print axioms UnifiedFactorization.relativeInput_broken_zero
#print axioms UnifiedFactorization.relativeInput_broken_one
#print axioms UnifiedFactorization.relativeInput_broken_two
#print axioms UnifiedFactorization.brokenReading_not_constant
#print axioms UnifiedFactorization.no_factorization_on_broken
