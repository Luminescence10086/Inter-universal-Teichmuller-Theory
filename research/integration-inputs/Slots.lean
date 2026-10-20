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
coincidence, and it is decidable at the level of the family.

The criterion is deliberately restricted to **slotwise (diagonal)** actions. It is
*not* a proof that non-diagonal actions cannot be equivariant: `mixingMap` below is a
genuinely slot-mixing `Q_p`-linear automorphism of two slots that **does** commute
with the slot swap, because it is symmetric. Equivariance of a mixing action has to be
checked separately; the diagonal criterion says nothing about it.

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

/-- Relabellings compose: applying `τ` first and then `σ` is relabelling by
`τ.trans σ`, since `Equiv.trans` applies its left argument first. No contravariance
is claimed beyond this writing convention. -/
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

/-! ## A mixing action that *is* equivariant

The diagonal criterion above must not be read as "only diagonal actions can be
equivariant". The symmetric two-slot map `(x₀, x₁) ↦ (2x₀ + x₁, x₀ + 2x₁)` mixes the
slots, is a genuine `Q_p`-linear automorphism (its matrix has determinant `3 ≠ 0` in
characteristic zero), and commutes with the slot swap. -/

/-- The slot-mixing map `(x₀, x₁) ↦ (2x₀ + x₁, x₀ + 2x₁)` on two slots. -/
def mixingMap : Tuple p 2 → Tuple p 2 :=
  fun x j => if j = 0 then 2 * x 0 + x 1 else x 0 + 2 * x 1

/-- Its inverse, `(1/3)·(2x₀ - x₁, -x₀ + 2x₁)`. -/
def mixingInv : Tuple p 2 → Tuple p 2 :=
  fun x j =>
    if j = 0 then (1 / 3) * (2 * x 0 - x 1) else (1 / 3) * (-x 0 + 2 * x 1)

/-- The mixing map is additive. -/
theorem mixingMap_add (x y : Tuple p 2) : mixingMap p (x + y) = mixingMap p x + mixingMap p y := by
  funext j
  fin_cases j <;> simp [mixingMap] <;> ring

/-- The mixing map is `Q_p`-homogeneous. -/
theorem mixingMap_smul (c : ℚ_[p]) (x : Tuple p 2) :
    mixingMap p (c • x) = c • mixingMap p x := by
  funext j
  fin_cases j <;> simp [mixingMap] <;> ring

/-- Left inverse law, using that `3` is invertible in `Q_p` (characteristic zero). -/
theorem mixingInv_left (x : Tuple p 2) : mixingInv p (mixingMap p x) = x := by
  have h3 : (3 : ℚ_[p]) ≠ 0 := by norm_num
  funext j
  fin_cases j <;>
    simp [mixingMap, mixingInv] <;>
    field_simp <;> ring

/-- Right inverse law. -/
theorem mixingInv_right (x : Tuple p 2) : mixingMap p (mixingInv p x) = x := by
  have h3 : (3 : ℚ_[p]) ≠ 0 := by norm_num
  funext j
  fin_cases j <;>
    simp [mixingMap, mixingInv] <;>
    field_simp <;> ring

/-- **A genuine `Q_p`-linear automorphism of two slots that mixes them.** -/
def mixingEquiv : Tuple p 2 ≃ₗ[ℚ_[p]] Tuple p 2 where
  toFun := mixingMap p
  map_add' := mixingMap_add p
  map_smul' := mixingMap_smul p
  invFun := mixingInv p
  left_inv := mixingInv_left p
  right_inv := mixingInv_right p

/-- **The mixing automorphism commutes with the slot swap.** So equivariance is not a
prerogative of diagonal actions, and the diagonal criterion above cannot be used to
rule out a mixing repair. -/
theorem mixingEquiv_commutes_swap (x : Tuple p 2) :
    relabel p (Equiv.swap 0 1) (mixingEquiv p x) =
      mixingEquiv p (relabel p (Equiv.swap 0 1) x) := by
  funext j
  fin_cases j <;>
    simp [mixingEquiv, mixingMap, relabel] <;> ring

/-- The mixing map is **not** a slotwise scalar action: the second component of the
image of the first basis tuple is nonzero, while any slotwise action would give zero. -/
theorem mixingMap_not_slotwise :
    ¬ ∃ a : Fin 2 → ℚ_[p], ∀ x : Tuple p 2, mixingMap p x = slotwise p a x := by
  rintro ⟨a, ha⟩
  have h := congrFun (ha (fun j => if j = 0 then (1 : ℚ_[p]) else 0)) 1
  simp [mixingMap, slotwise] at h

end

end IUTBridge.Slots
