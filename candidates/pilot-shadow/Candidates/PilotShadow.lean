import Mathlib.Data.Fintype.Perm
import IUTBridge.Slots

/-!
# The arithmetic shadow of the repository's 4-slot pilot pattern

`IUTAudit/LocalNumerics.lean` models the pilot tuple as an abstract 4-slot pattern
`(b₁, b₁, b₂, b₁)` over an arbitrary type `B`. This file makes the *valuation vector* of that
pattern an actual object over `ℤ`, computes its orbit under slot permutations, its rectangular
hull (the coordinatewise minimum), and the exact excess that the hull introduces.

## Scope, stated plainly

* This file studies **valuation vectors under slot permutations**. It is the arithmetic shadow
  of the combinatorial pilot pattern only.
* `b₁` and `b₂` here are **integers (valuation thresholds)**. They are **not places of a real
  Hodge theater**, not local fields, not labels of an actual pilot structure.
* The results below do **not** construct a pilot, a Θ-link, an `Ism`, or any IUT object, and
  they **close no gap** in any argument about IUT. Nothing here is a statement about Step (v)
  or about the actual content of the theory.
* `b₁ ≠ b₂` is assumed exactly where the combinatorics need it (the orbit has four points only
  when the two values are distinct); in that case `b₁` and `b₂` play the role of the two
  abstract places of the pilot pattern, nothing more.

## The action convention (fixed once)

For a permutation `σ : Equiv.Perm (Fin n)` of the slots and a vector `e : Fin n → ℤ`, the label
action is

`(σ • e) j = e (σ.symm j)`

i.e. the *target* slot `j` reads the *source* slot `σ⁻¹ j`. This is exactly the convention of
`IUTBridge.Slots.relabel` (see `relabel_toPadic` below), and `Equiv.swap 2 3` is the label
action used by the repository's `swap23` checks (`swap23_eq_labelAction`).

## Why the hull is a coordinatewise `min`

The valuation vector is a vector of *thresholds*: coordinate `j` records the largest valuation
at which slot `j` is allowed to be non-trivial. A **larger** threshold means a **smaller** box
(more divisibility is demanded). The rectangular hull of an orbit is therefore the
coordinatewise **minimum** of the thresholds, not the maximum: it is the largest box that
contains every member of the orbit. The excess measured below is exactly the mismatch between
this rectangular envelope and the profile.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Candidates.PilotShadow

/-! ## 1. The label action and the profile -/

/-- The label action on integer valuation vectors, with the fixed convention
`(σ • e) j = e (σ.symm j)`: the target slot `j` reads the source slot `σ⁻¹ j`. This is the
same convention as `IUTBridge.Slots.relabel`, transported from `ℚ_[p]`-tuples to `ℤ`-vectors. -/
def act {n : Nat} (σ : Equiv.Perm (Fin n)) (e : Fin n → ℤ) : Fin n → ℤ := fun j => e (σ.symm j)

/-- The defining equation of the action. -/
theorem act_apply {n : Nat} (σ : Equiv.Perm (Fin n)) (e : Fin n → ℤ) (j : Fin n) :
    act σ e j = e (σ.symm j) := rfl

/-- The identity permutation acts trivially. -/
theorem act_one {n : Nat} (e : Fin n → ℤ) : act 1 e = e := rfl

/-- The action composes contravariantly, matching `IUTBridge.Slots.relabel_trans`. -/
theorem act_trans {n : Nat} (σ τ : Equiv.Perm (Fin n)) (e : Fin n → ℤ) :
    act σ (act τ e) = act (τ.trans σ) e := rfl

/-- `IUTBridge.Slots.swap23` is literally the label action `Equiv.swap 2 3` used throughout
this file. This is the reuse of the repository's `swap23`. -/
theorem swap23_eq_labelAction : IUTBridge.Slots.swap23 = Equiv.swap 2 3 := rfl

/-- The integer action of this file obeys exactly the slot convention of
`IUTBridge.Slots.relabel`: casting a `ℤ`-valued vector pointwise into `ℚ_[p]` intertwines the
two actions. This is the formal link between the integer shadow and the repository's p-adic
relabelling; it says nothing about IUT. -/
theorem relabel_toPadic {n : Nat} (p : Nat) [Fact p.Prime] (σ : Equiv.Perm (Fin n))
    (e : Fin n → ℤ) :
    IUTBridge.Slots.relabel p σ (fun j => (e j : ℚ_[p])) = fun j => (act σ e j : ℚ_[p]) := rfl

/-- The valuation vector of the pilot pattern `(b₁, b₁, b₂, b₁)` over `ℤ`: slot `2` carries
`v₂`, every other slot carries `v₁`. The two integers are **valuation thresholds**, not places
of a Hodge theater. -/
def pilotProfile (v₁ v₂ : ℤ) : Fin 4 → ℤ := fun j => if j = 2 then v₂ else v₁

/-- The same pattern with the exceptional value placed at an arbitrary slot `k`. This is only a
bookkeeping device: it is what the label action does to `pilotProfile`. -/
def slotVector (v₁ v₂ : ℤ) (k : Fin 4) : Fin 4 → ℤ := fun j => if j = k then v₂ else v₁

/-- The profile is the slot vector with the exceptional value in slot `2`. -/
theorem pilotProfile_eq_slotVector (v₁ v₂ : ℤ) :
    pilotProfile v₁ v₂ = slotVector v₁ v₂ 2 := rfl

/-- The slot vector reads `v₂` at its own slot. -/
theorem slotVector_self (v₁ v₂ : ℤ) (k : Fin 4) : slotVector v₁ v₂ k k = v₂ := by
  simp [slotVector]

/-- The slot vector reads `v₁` away from its own slot. -/
theorem slotVector_of_ne {v₁ v₂ : ℤ} {k j : Fin 4} (h : j ≠ k) :
    slotVector v₁ v₂ k j = v₁ := by
  simp [slotVector, h]

/-- A slot vector takes only the two values `v₁` and `v₂`. -/
theorem slotVector_apply_or (v₁ v₂ : ℤ) (k j : Fin 4) :
    slotVector v₁ v₂ k j = v₁ ∨ slotVector v₁ v₂ k j = v₂ := by
  by_cases h : j = k
  · refine Or.inr ?_
    rw [h]
    exact slotVector_self v₁ v₂ k
  · exact Or.inl (slotVector_of_ne h)

/-- When `v₁ ≠ v₂`, the value `v₂` marks the exceptional slot and nothing else. -/
theorem slotVector_eq_v₂_iff {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) (k j : Fin 4) :
    slotVector v₁ v₂ k j = v₂ ↔ j = k := by
  by_cases hj : j = k
  · subst hj
    exact ⟨fun _ => rfl, fun _ => slotVector_self v₁ v₂ j⟩
  · have hval : slotVector v₁ v₂ k j = v₁ := slotVector_of_ne hj
    rw [hval]
    exact ⟨fun hv => absurd hv h, fun hk => absurd hk hj⟩

/-- Placing `v₂` in a slot is injective in the slot, as soon as `v₁ ≠ v₂`. This is what makes
the label action collapse a whole stabiliser on the profile. -/
theorem slotVector_injective {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) :
    Function.Injective (slotVector v₁ v₂) := by
  intro k l hkl
  by_contra hne
  have hk : slotVector v₁ v₂ k k = v₂ := slotVector_self v₁ v₂ k
  have hl : slotVector v₁ v₂ l k = v₁ := slotVector_of_ne hne
  have hval : slotVector v₁ v₂ k k = slotVector v₁ v₂ l k := by rw [hkl]
  rw [hk, hl] at hval
  exact h hval.symm

/-! ## 2. The orbit of the profile -/

/-- The permutation orbit of a valuation vector, as a finite set of vectors. -/
noncomputable def orbit {n : Nat} (e : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => act σ e)

/-- Every orbit contains its own vector. -/
theorem orbit_nonempty {n : Nat} (e : Fin n → ℤ) : (orbit e).Nonempty := by
  refine ⟨e, ?_⟩
  simp only [orbit]
  exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, act_one e⟩

/-- The label action sends the profile to the slot vector indexed by the image of slot `2`. -/
theorem act_pilotProfile {v₁ v₂ : ℤ} (σ : Equiv.Perm (Fin 4)) :
    act σ (pilotProfile v₁ v₂) = slotVector v₁ v₂ (σ 2) := by
  funext j
  have hiff : σ.symm j = 2 ↔ j = σ 2 := Equiv.symm_apply_eq σ
  simp only [act, pilotProfile, slotVector]
  exact if_congr hiff rfl rfl

/-- The orbit is invariant under the label action: acting does not leave the orbit. -/
theorem orbit_act {n : Nat} (σ : Equiv.Perm (Fin n)) (e : Fin n → ℤ) :
    orbit (act σ e) = orbit e := by
  apply Finset.ext
  intro f
  simp only [orbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨σ.trans τ, by rw [← act_trans τ σ e]; exact hτ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨σ.symm.trans τ, ?_⟩
    have hperm : σ.trans (σ.symm.trans τ) = τ := by
      ext x
      simp
    rw [act_trans, hperm]
    exact hτ

/-- Every slot vector is the label action of the profile by the transposition `2 ↔ k`. -/
theorem slotVector_eq_act (v₁ v₂ : ℤ) (k : Fin 4) :
    slotVector v₁ v₂ k = act (Equiv.swap 2 k) (pilotProfile v₁ v₂) := by
  rw [act_pilotProfile, Equiv.swap_apply_left]

/-- The orbit of the profile consists exactly of the four slot vectors. -/
theorem orbit_slotVector (v₁ v₂ : ℤ) (k : Fin 4) :
    orbit (slotVector v₁ v₂ k) = orbit (pilotProfile v₁ v₂) := by
  rw [slotVector_eq_act, orbit_act]

/-- Membership in the orbit of the profile is exactly "`e` is a slot vector". -/
theorem mem_orbit_iff_exists_slotVector (v₁ v₂ : ℤ) (e : Fin 4 → ℤ) :
    e ∈ orbit (pilotProfile v₁ v₂) ↔ ∃ k : Fin 4, slotVector v₁ v₂ k = e := by
  constructor
  · intro he
    simp only [orbit, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨σ, hσ⟩ := he
    exact ⟨σ 2, by rw [← hσ, act_pilotProfile]⟩
  · rintro ⟨k, rfl⟩
    rw [slotVector_eq_act]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- **Target 2.** For `v₁ ≠ v₂`, a vector lies in the permutation orbit of the profile iff every
coordinate is `v₁` or `v₂` and exactly one coordinate equals `v₂`.

This is a statement about integer valuation vectors only. It constructs no pilot, no Θ-link, no
`Ism`, and closes no gap. -/
theorem orbit_mem_iff {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) (e : Fin 4 → ℤ) :
    e ∈ orbit (pilotProfile v₁ v₂) ↔
      (∀ j : Fin 4, e j = v₁ ∨ e j = v₂) ∧ ∃! j : Fin 4, e j = v₂ := by
  constructor
  · intro he
    obtain ⟨k, rfl⟩ := (mem_orbit_iff_exists_slotVector v₁ v₂ e).mp he
    refine ⟨fun j => slotVector_apply_or v₁ v₂ k j, k, slotVector_self v₁ v₂ k, ?_⟩
    intro j hj
    exact (slotVector_eq_v₂_iff h k j).mp hj
  · rintro ⟨hall, j0, hj0, huniq⟩
    rw [mem_orbit_iff_exists_slotVector]
    refine ⟨j0, ?_⟩
    funext j
    by_cases hj : j = j0
    · subst hj
      have hval : slotVector v₁ v₂ j j = v₂ := slotVector_self v₁ v₂ j
      rw [hval]
      exact hj0.symm
    · have hne : e j ≠ v₂ := fun hc => hj (huniq j hc)
      have hv1 : e j = v₁ := by
        rcases hall j with hv | hv
        · exact hv
        · exact absurd hv hne
      have hval : slotVector v₁ v₂ j0 j = v₁ := slotVector_of_ne hj
      rw [hval, hv1]

/-- **Target 3.** For `v₁ ≠ v₂` the orbit of the profile has exactly four elements: the
permutation orbit is the four slot vectors, and the slot is recoverable from the vector.

This counts valuation vectors only; it constructs no pilot, no Θ-link, no `Ism`, and closes no
gap. -/
theorem orbit_card {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) : (orbit (pilotProfile v₁ v₂)).card = 4 := by
  have himg : orbit (pilotProfile v₁ v₂) = Finset.univ.image (slotVector v₁ v₂) := by
    apply Finset.ext
    intro e
    rw [mem_orbit_iff_exists_slotVector]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rw [himg, Finset.card_image_of_injective _ (slotVector_injective h)]
  simp

/-! ## 3. The rectangular hull and its excess -/

/-- The rectangular hull of the orbit: coordinatewise **minimum** of the thresholds. A larger
threshold means a smaller box, so the minimum is the largest box that still contains the whole
orbit. -/
noncomputable def hull {n : Nat} (e : Fin n → ℤ) : Fin n → ℤ :=
  fun j => (orbit e).inf' (orbit_nonempty e) (fun f => f j)

/-- The hull is below every member of the orbit, coordinate by coordinate. -/
theorem hull_le_of_mem {n : Nat} {e f : Fin n → ℤ} (hf : f ∈ orbit e) (j : Fin n) :
    hull e j ≤ f j :=
  Finset.inf'_le (fun g => g j) hf

/-- The hull is above any integer lying below every member of the orbit, coordinate by
coordinate. -/
theorem le_hull {n : Nat} {e : Fin n → ℤ} {a : ℤ} (j : Fin n)
    (h : ∀ f ∈ orbit e, a ≤ f j) : a ≤ hull e j :=
  Finset.le_inf' (orbit_nonempty e) (fun f => f j) h

/-- Every member of the orbit takes only the two values `v₁`, `v₂` in every coordinate. -/
theorem orbit_coord_value {v₁ v₂ : ℤ} (j : Fin 4) {f : Fin 4 → ℤ}
    (hf : f ∈ orbit (pilotProfile v₁ v₂)) : f j = v₁ ∨ f j = v₂ := by
  simp only [orbit, Finset.mem_image, Finset.mem_univ, true_and] at hf
  obtain ⟨σ, hσ⟩ := hf
  rw [← hσ, act_pilotProfile]
  exact slotVector_apply_or v₁ v₂ (σ 2) j

/-- In every coordinate the orbit attains the value `v₁`. -/
theorem exists_orbit_coord_eq_v₁ (v₁ v₂ : ℤ) (j : Fin 4) :
    ∃ f ∈ orbit (pilotProfile v₁ v₂), f j = v₁ := by
  have hne : j ≠ (if j = 2 then (3 : Fin 4) else 2) := by
    by_cases hj : j = 2
    · subst hj
      rw [ite_eq_left rfl]
      decide
    · rw [ite_eq_right hj]
      exact hj
  refine ⟨slotVector v₁ v₂ (if j = 2 then 3 else 2), ?_, slotVector_of_ne hne⟩
  rw [slotVector_eq_act]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- In every coordinate the orbit attains the value `v₂`. -/
theorem exists_orbit_coord_eq_v₂ (v₁ v₂ : ℤ) (j : Fin 4) :
    ∃ f ∈ orbit (pilotProfile v₁ v₂), f j = v₂ := by
  refine ⟨slotVector v₁ v₂ j, ?_, slotVector_self v₁ v₂ j⟩
  rw [slotVector_eq_act]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- **Target 4.** The hull of the orbit is the constant vector `fun _ => min v₁ v₂`: every
coordinate of the rectangular envelope sits at the smaller of the two thresholds, independently
of which slot carried `v₂`. This is the coordinatewise `min` because a larger valuation
threshold is a smaller box.

This is still bookkeeping for integer thresholds; it constructs no pilot, no Θ-link, no `Ism`,
and closes no gap. -/
theorem hull_eq (v₁ v₂ : ℤ) : hull (pilotProfile v₁ v₂) = fun _ => min v₁ v₂ := by
  funext j
  apply le_antisymm
  · rcases le_total v₁ v₂ with hle | hle
    · obtain ⟨f, hf, hval⟩ := exists_orbit_coord_eq_v₁ v₁ v₂ j
      calc hull (pilotProfile v₁ v₂) j ≤ f j := hull_le_of_mem hf j
        _ = v₁ := hval
        _ = min v₁ v₂ := (min_eq_left hle).symm
    · obtain ⟨f, hf, hval⟩ := exists_orbit_coord_eq_v₂ v₁ v₂ j
      calc hull (pilotProfile v₁ v₂) j ≤ f j := hull_le_of_mem hf j
        _ = v₂ := hval
        _ = min v₁ v₂ := (min_eq_right hle).symm
  · refine le_hull j ?_
    intro f hf
    rcases orbit_coord_value j hf with hh | hh
    · rw [hh]
      exact min_le_left _ _
    · rw [hh]
      exact min_le_right _ _

/-- The hull of *any* slot vector is the same constant vector: the hull forgets which slot
carried `v₂`. -/
theorem hull_slotVector (v₁ v₂ : ℤ) (k : Fin 4) :
    hull (slotVector v₁ v₂ k) = fun _ => min v₁ v₂ := by
  funext j
  apply le_antisymm
  · rcases le_total v₁ v₂ with hle | hle
    · obtain ⟨f, hf, hval⟩ := exists_orbit_coord_eq_v₁ v₁ v₂ j
      have hf' : f ∈ orbit (slotVector v₁ v₂ k) := by
        rw [orbit_slotVector]
        exact hf
      calc hull (slotVector v₁ v₂ k) j ≤ f j := hull_le_of_mem hf' j
        _ = v₁ := hval
        _ = min v₁ v₂ := (min_eq_left hle).symm
    · obtain ⟨f, hf, hval⟩ := exists_orbit_coord_eq_v₂ v₁ v₂ j
      have hf' : f ∈ orbit (slotVector v₁ v₂ k) := by
        rw [orbit_slotVector]
        exact hf
      calc hull (slotVector v₁ v₂ k) j ≤ f j := hull_le_of_mem hf' j
        _ = v₂ := hval
        _ = min v₁ v₂ := (min_eq_right hle).symm
  · refine le_hull j ?_
    intro f hf
    have hf' : f ∈ orbit (pilotProfile v₁ v₂) := by
      rw [← orbit_slotVector]
      exact hf
    rcases orbit_coord_value j hf' with hh | hh
    · rw [hh]
      exact min_le_left _ _
    · rw [hh]
      exact min_le_right _ _

/-- **Target 5.** If `v₁ < v₂`, the hull is strictly below the profile in exactly one
coordinate, namely slot `2`: the set of coordinates where the hull is strictly below the
profile is exactly `{2}`. This is the precise sense in which the rectangular envelope's excess
is one slot.

The statement is about integer thresholds. It does not construct a pilot, a Θ-link, an `Ism`,
or any IUT object, and it closes no gap. -/
theorem hull_strict_one_coordinate (v₁ v₂ : ℤ) (h : v₁ < v₂) :
    {j : Fin 4 | hull (pilotProfile v₁ v₂) j < pilotProfile v₁ v₂ j} = {2} := by
  ext j
  rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, hull_eq, min_eq_left (le_of_lt h)]
  by_cases hj : j = 2
  · subst hj
    have hp : pilotProfile v₁ v₂ 2 = v₂ := by
      simp [pilotProfile]
    rw [hp]
    exact iff_of_true h rfl
  · have hp : pilotProfile v₁ v₂ j = v₁ := by
      simp [pilotProfile, hj]
    rw [hp]
    exact ⟨fun hlt => absurd hlt (lt_irrefl v₁), fun hc => absurd hc hj⟩

/-! ## 4. The label action does not preserve the pattern -/

/-- The label action `Equiv.swap 2 3` on the profile: slot `3` receives `v₂`. -/
theorem act_swap23_profile {v₁ v₂ : ℤ} :
    act IUTBridge.Slots.swap23 (pilotProfile v₁ v₂) = slotVector v₁ v₂ 3 := by
  rw [swap23_eq_labelAction, act_pilotProfile, Equiv.swap_apply_left]

/-- The label action moves the exceptional value from slot `2` to slot `3`, exactly as
`IUTBridge.Slots.swap23_exchanges_high_slots` does for p-adic tuples. -/
theorem swap23_profile_high_slots {v₁ v₂ : ℤ} :
    act IUTBridge.Slots.swap23 (pilotProfile v₁ v₂) 2 = v₁ ∧
      act IUTBridge.Slots.swap23 (pilotProfile v₁ v₂) 3 = v₂ := by
  rw [act_swap23_profile]
  exact ⟨slotVector_of_ne (by decide), slotVector_self v₁ v₂ 3⟩

/-- The label action leaves slots `0` and `1` alone, exactly as
`IUTBridge.Slots.swap23_fixes_low_slots` does for p-adic tuples. -/
theorem swap23_profile_low_slots {v₁ v₂ : ℤ} :
    act IUTBridge.Slots.swap23 (pilotProfile v₁ v₂) 0 = v₁ ∧
      act IUTBridge.Slots.swap23 (pilotProfile v₁ v₂) 1 = v₁ := by
  rw [act_swap23_profile]
  exact ⟨slotVector_of_ne (by decide), slotVector_of_ne (by decide)⟩

/-- **Target 6.** For `v₁ ≠ v₂` the label action `Equiv.swap 2 3` does **not** preserve the
pilot profile: it moves the exceptional slot from `2` to `3`. So the pattern is not invariant
under the label action, even though its hull is.

Integer thresholds only: no pilot, no Θ-link, no `Ism`, no IUT object, no gap closed. -/
theorem swap23_moves_profile {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) :
    act (Equiv.swap 2 3) (pilotProfile v₁ v₂) ≠ pilotProfile v₁ v₂ := by
  rw [act_pilotProfile, Equiv.swap_apply_left, pilotProfile_eq_slotVector]
  intro heq
  exact absurd (slotVector_injective h heq) (by decide)

/-! ## 5. The hull forgets the slot -/

/-- **Target 7.** The excess introduced by the rectangular hull is uniform: the hull of every
slot vector is the same constant vector, the hull is invariant under the label action
`swap 2 3`, and yet the profile itself is not invariant.

So "which slot carried `v₂`" is invisible to the envelope but decisive for the profile: this is
exactly the arithmetic shadow of the obstruction, and nothing more. It constructs no pilot, no
Θ-link, no `Ism`, and closes no gap. -/
theorem excess_is_uniform {v₁ v₂ : ℤ} (h : v₁ ≠ v₂) :
    (∀ k : Fin 4, hull (slotVector v₁ v₂ k) = fun _ => min v₁ v₂) ∧
      hull (act (Equiv.swap 2 3) (pilotProfile v₁ v₂)) = hull (pilotProfile v₁ v₂) ∧
      act (Equiv.swap 2 3) (pilotProfile v₁ v₂) ≠ pilotProfile v₁ v₂ := by
  refine ⟨fun k => hull_slotVector v₁ v₂ k, ?_, swap23_moves_profile h⟩
  rw [act_pilotProfile, Equiv.swap_apply_left, hull_slotVector, hull_eq]

end Candidates.PilotShadow
