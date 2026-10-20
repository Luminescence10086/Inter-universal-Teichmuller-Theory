import IUTBridge.ScaleLedger

/-!
# Slot relabelling versus slotwise scalar action, on actual p-adic tuples

Round 5 left a specific question open: how a synchronization condition attached to
each place could be independent of the label. This module answers the *toy version*
of that question on actual arithmetic data.

A tuple of actual `Q_p` numbers indexed by `Fin n` carries two commuting candidate
actions:

* **relabelling** by a permutation `σ` of the slots;
* **slotwise scalar action** by a family `a : Fin n → Q_p`.

Main result: relabelling conjugates a slotwise scalar family. Consequently a
slotwise action is `σ`-equivariant **iff** the scalar family is invariant under `σ`.
So "synchronization" is exactly invariance of a scalar family, not a label-by-label
coincidence, and it is decidable at the level of the family. A slot-mixing action has
no such property, which is why the commutativity argument cannot be reused for it.

Scope. These are tuples of p-adic numbers with explicit permutation and scalar
actions. There is no IUT packet, no Kummer isomorphism, no seed region and no
Theta-link here; the label set is an abstract `Fin n`, not the slot set of a real
Hodge theater. Nothing is concluded about the Step (v) objection.
-/

set_option autoImplicit false

namespace IUTBridge.Slots

noncomputable section

variable (p : Nat) [hp : Fact p.Prime]

/-- A tuple of actual p-adic numbers indexed by a finite slot set. -/
abbrev Tuple (n : Nat) : Type := Fin n → ℚ_[p]

/-- Relabelling: the component at target slot `j` is the source component at `σ⁻¹ j`. -/
def relabel {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Tuple p n) : Tuple p n :=
  fun j => x (σ.symm j)

/-- Slotwise scalar action: slot `j` is multiplied by `a j`. -/
def slotwise {n : Nat} (a : Fin n → ℚ_[p]) (x : Tuple p n) : Tuple p n :=
  fun j => a j * x j

/-- Relabelling is injective on tuples: no component is lost or duplicated. -/
theorem relabel_injective {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (relabel p σ) := by
  intro x y h
  funext i
  have := congrFun h (σ i)
  simpa [relabel] using this

/-- Relabellings compose contravariantly: relabelling by `σ` then `τ` relabels by
`τ.trans σ` in the direction that keeps the projection formula clean. -/
theorem relabel_trans {n : Nat} (σ τ : Equiv.Perm (Fin n)) (x : Tuple p n) :
    relabel p σ (relabel p τ x) = relabel p (τ.trans σ) x := by
  funext j
  rfl

/-- **Projection formula (toy level).** Relabelling transports a slotwise scalar
action into the conjugated scalar family: the action after relabelling is the
conjugate of the original one. This is the structural analogue of a projection
equation for a joint lift; it is proved here for actual p-adic tuples only. -/
theorem relabel_slotwise {n : Nat} (σ : Equiv.Perm (Fin n)) (a : Fin n → ℚ_[p])
    (x : Tuple p n) :
    relabel p σ (slotwise p a x) = slotwise p (fun j => a (σ.symm j)) (relabel p σ x) := by
  funext j
  rfl

/-- Valuation bookkeeping for the transported slotwise action, with the explicit
nonzero premises that a finite p-adic valuation requires. -/
theorem valuation_relabel_slotwise {n : Nat} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) (x : Tuple p n) (j : Fin n)
    (ha : a (σ.symm j) ≠ 0) (hx : x (σ.symm j) ≠ 0) :
    (relabel p σ (slotwise p a x) j).valuation =
      (a (σ.symm j)).valuation + (x (σ.symm j)).valuation := by
  show (a (σ.symm j) * x (σ.symm j)).valuation = _
  exact Padic.valuation_mul ha hx

/-- A slotwise scalar action with a `σ`-invariant family commutes with relabelling. -/
theorem slotwise_commutes_of_invariant {n : Nat} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) (h : ∀ j : Fin n, a (σ.symm j) = a j) (x : Tuple p n) :
    relabel p σ (slotwise p a x) = slotwise p a (relabel p σ x) := by
  funext j
  simp only [relabel, slotwise, h j]

/-- **Synchronization is exactly invariance of the scalar family.** If some slot
receives a different scalar from its preimage under `σ`, then the slotwise action
does not commute with relabelling, and the constant-one tuple witnesses it. -/
theorem slotwise_not_commutes_of_witness {n : Nat} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) (j : Fin n) (h : a (σ.symm j) ≠ a j) :
    ∃ x : Tuple p n, relabel p σ (slotwise p a x) ≠ slotwise p a (relabel p σ x) := by
  refine ⟨fun _ => 1, ?_⟩
  intro hcomm
  have hval := congrFun hcomm j
  simp only [relabel, slotwise, mul_one] at hval
  exact h hval

/-- Uniform scaling by a single p-adic scalar commutes with **every** relabelling,
because a constant family is invariant under every permutation. -/
theorem uniform_scale_commutes {n : Nat} (σ : Equiv.Perm (Fin n)) (c : ℚ_[p])
    (x : Tuple p n) :
    relabel p σ (slotwise p (fun _ => c) x) =
      slotwise p (fun _ => c) (relabel p σ x) :=
  slotwise_commutes_of_invariant p σ (fun _ => c) (fun _ => rfl) x

/-- The concrete swap `2 ↔ 3` on four slots, the label action used by the integer
model of the repository's `swap23` checks. -/
def swap23 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

/-- Under `swap23`, slots `0` and `1` are untouched by the label action. -/
theorem swap23_fixes_low_slots (x : Tuple p 4) :
    relabel p swap23 x 0 = x 0 ∧ relabel p swap23 x 1 = x 1 := by
  constructor <;> rfl

/-- Under `swap23`, slots `2` and `3` exchange their components. -/
theorem swap23_exchanges_high_slots (x : Tuple p 4) :
    relabel p swap23 x 2 = x 3 ∧ relabel p swap23 x 3 = x 2 := by
  constructor <;> rfl

end

end IUTBridge.Slots
