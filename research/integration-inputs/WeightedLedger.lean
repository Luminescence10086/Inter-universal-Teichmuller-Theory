import IUTBridge.Slots

/-!
# Weighted valuation ledger: which label actions preserve it

Round one built two separate facts: a slotwise scalar action is transported by a
label permutation into the conjugated family (`IUTBridge.Slots`), and a scaling
moves the p-adic valuation by an exact integer (`IUTBridge.ScaleLedger`). This
module puts them together into a single **weighted ledger** and asks the sharp
question the pilot data poses:

> For which label actions `σ` is the weighted total `Σ_j w_j · v(x_j)` invariant?

The answer is exact and proved in both directions: the weighted ledger is
`σ`-invariant for *every* tuple **iff** the weight vector is `σ`-invariant. So:

* the unweighted total (`w ≡ 1`) is invariant under **every** label action — the
  label action moves per-slot data but not the total;
* the pilot-style weight vector `(1,1,2,1)` is **not** invariant under the swap
  `2 ↔ 3`, and a concrete tuple witnesses the failure;
* a symmetric weight vector is invariant, so the question is decidable on the
  weight vector alone, before any tuple is chosen.

Scope. The slots are an abstract `Fin n`, the weights are arbitrary integers, and
the tuples are actual `Q_p` numbers. No Ism/Kummer element, packet, seed region or
Arakelov log-volume is constructed, and nothing here decides the Step (v)
objection. The ledger is the exact integer bookkeeping of the base field.
-/

set_option autoImplicit false

open scoped Pointwise BigOperators

namespace IUTBridge.WeightedLedger

noncomputable section

variable (p : Nat) [hp : Fact p.Prime]

/-- The p-adic valuation profile of a tuple. Mathlib's valuation of `0` is `0`, so
this is a total function; multiplicativity below states its nonzero premises. -/
def vprofile {n : Nat} (x : IUTBridge.Slots.Tuple p n) (j : Fin n) : Int :=
  (x j).valuation

/-- The weighted valuation ledger of a tuple: the quantity a comparison of
weighted averages actually consumes. -/
def weightedLedger {n : Nat} (w : Fin n → Int) (x : IUTBridge.Slots.Tuple p n) : Int :=
  ∑ j, w j * vprofile p x j

/-- The unweighted total ledger, i.e. the weight vector `1`. -/
def totalLedger {n : Nat} (x : IUTBridge.Slots.Tuple p n) : Int :=
  weightedLedger p (fun _ => 1) x

/-- Relabelling permutes the valuation profile. -/
theorem vprofile_relabel {n : Nat} (σ : Equiv.Perm (Fin n))
    (x : IUTBridge.Slots.Tuple p n) (j : Fin n) :
    vprofile p (IUTBridge.Slots.relabel p σ x) j = vprofile p x (σ.symm j) := rfl

/-- A slotwise scalar action shifts the profile by the scalar's valuation. -/
theorem vprofile_slotwise {n : Nat} (a : Fin n → ℚ_[p]) (x : IUTBridge.Slots.Tuple p n)
    (j : Fin n) (ha : a j ≠ 0) (hx : x j ≠ 0) :
    vprofile p (IUTBridge.Slots.slotwise p a x) j = (a j).valuation + vprofile p x j :=
  Padic.valuation_mul ha hx

/-- Reindexing a full sum along a permutation. -/
theorem sum_perm {n : Nat} (σ : Equiv.Perm (Fin n)) (f : Fin n → Int) :
    (∑ j, f (σ j)) = ∑ j, f j :=
  Equiv.sum_comp σ f

/-- **The ledger under relabelling.** The weighted ledger of the relabelled tuple
is the ledger of the original tuple read with the permuted weights. -/
theorem weightedLedger_relabel {n : Nat} (σ : Equiv.Perm (Fin n)) (w : Fin n → Int)
    (x : IUTBridge.Slots.Tuple p n) :
    weightedLedger p w (IUTBridge.Slots.relabel p σ x) =
      ∑ j, w (σ j) * vprofile p x j := by
  have h1 : weightedLedger p w (IUTBridge.Slots.relabel p σ x) =
      ∑ j, w j * vprofile p x (σ.symm j) := by
    simp only [weightedLedger, vprofile_relabel]
  rw [h1]
  simpa using Equiv.sum_comp (σ.symm) (fun k => w (σ k) * vprofile p x k)

/-- **The ledger under a slotwise scalar action.** The weighted ledger shifts by
the weighted sum of the scalar valuations: no other term appears. -/
theorem weightedLedger_slotwise {n : Nat} (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (x : IUTBridge.Slots.Tuple p n) (ha : ∀ j, a j ≠ 0) (hx : ∀ j, x j ≠ 0) :
    weightedLedger p w (IUTBridge.Slots.slotwise p a x) =
      weightedLedger p w x + ∑ j, w j * (a j).valuation := by
  simp only [weightedLedger]
  have hv : ∀ j : Fin n,
      vprofile p (IUTBridge.Slots.slotwise p a x) j = (a j).valuation + vprofile p x j :=
    fun j => vprofile_slotwise p a x j (ha j) (hx j)
  simp only [hv, mul_add]
  rw [Finset.sum_add_distrib]
  exact add_comm _ _

/-- Uniform rescaling by `p^k` shifts the weighted ledger by `k · Σ w`. -/
theorem weightedLedger_uniform {n : Nat} (w : Fin n → Int) (k : Int)
    (x : IUTBridge.Slots.Tuple p n) (hx : ∀ j, x j ≠ 0) :
    weightedLedger p w
        (IUTBridge.Slots.slotwise p (fun _ => (p : ℚ_[p]) ^ k) x) =
      weightedLedger p w x + k * ∑ j, w j := by
  have ha : ∀ j : Fin n, ((p : ℚ_[p]) ^ k) ≠ 0 :=
    fun _ => zpow_ne_zero k (IUTBridge.ScaleLedger.p_ne_zero p)
  rw [weightedLedger_slotwise p w _ x ha hx]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Padic.valuation_zpow, Padic.valuation_p, mul_one, mul_comm]

/-- The unit-at-one-slot tuple: its profile is the indicator of one slot. -/
def deltaTuple {n : Nat} (i : Fin n) : IUTBridge.Slots.Tuple p n :=
  fun j => (p : ℚ_[p]) ^ (if j = i then (1 : Int) else 0)

/-- The profile of the delta tuple is the indicator function. -/
theorem vprofile_delta {n : Nat} (i : Fin n) :
    vprofile p (deltaTuple p i) = fun j => if j = i then (1 : Int) else 0 := by
  funext j
  simp only [vprofile, deltaTuple]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- The weighted ledger of the delta tuple is the weight of its slot. -/
theorem weightedLedger_delta {n : Nat} (w : Fin n → Int) (i : Fin n) :
    weightedLedger p w (deltaTuple p i) = w i := by
  simp only [weightedLedger, vprofile_delta]
  have hzero : ∀ j ∈ Finset.univ, j ≠ i → w j * (if j = i then (1 : Int) else 0) = 0 := by
    intro j _ hj
    simp [hj]
  rw [Finset.sum_eq_single i hzero (by
    intro hi
    exact absurd (Finset.mem_univ i) hi)]
  simp

/-- **The exact invariance criterion.** The weighted ledger is invariant under a
label action for every tuple **iff** the weight vector is invariant under it. -/
theorem weightedLedger_invariant_iff {n : Nat} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Int) :
    (∀ x : IUTBridge.Slots.Tuple p n,
        weightedLedger p w (IUTBridge.Slots.relabel p σ x) = weightedLedger p w x) ↔
      ∀ j : Fin n, w (σ j) = w j := by
  constructor
  · intro h j
    have hw := h (deltaTuple p j)
    rw [weightedLedger_relabel, vprofile_delta] at hw
    have hleft : (∑ i, w (σ i) * (if i = j then (1 : Int) else 0)) = w (σ j) := by
      have hzero : ∀ i ∈ Finset.univ, i ≠ j → w (σ i) * (if i = j then (1 : Int) else 0) = 0 := by
        intro i _ hi
        simp [hi]
      rw [Finset.sum_eq_single j hzero (by
        intro hj
        exact absurd (Finset.mem_univ j) hj)]
      simp
    rw [hleft, weightedLedger_delta] at hw
    exact hw
  · intro hw x
    rw [weightedLedger_relabel]
    simp only [weightedLedger]
    exact Finset.sum_congr rfl fun j _ => by rw [hw j]

/-- **The unweighted total is label-invariant.** No condition on the permutation is
needed: the total ledger cannot see a relabelling. -/
theorem totalLedger_relabel {n : Nat} (σ : Equiv.Perm (Fin n))
    (x : IUTBridge.Slots.Tuple p n) :
    totalLedger p (IUTBridge.Slots.relabel p σ x) = totalLedger p x := by
  simp only [totalLedger, weightedLedger, vprofile_relabel, one_mul]
  exact Equiv.sum_comp σ.symm (fun j => vprofile p x j)

/-- A symmetric weight vector makes the ledger label-invariant, so partial symmetry
is decided on the weight vector alone. -/
theorem weightedLedger_invariant_of_symm {n : Nat} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Int) (hw : ∀ j, w (σ j) = w j) (x : IUTBridge.Slots.Tuple p n) :
    weightedLedger p w (IUTBridge.Slots.relabel p σ x) = weightedLedger p w x :=
  (weightedLedger_invariant_iff p σ w).mpr hw x

/-- **The pilot-style weight vector.** Weights `(1,1,2,1)` on four slots: the
non-uniform pattern a weighted comparison has to carry. -/
def pilotWeights : Fin 4 → Int := fun j => if j = 2 then 2 else 1

/-- The pilot-style weights are not invariant under the swap `2 ↔ 3`. -/
theorem pilotWeights_not_invariant :
    ¬ ∀ j : Fin 4, pilotWeights (IUTBridge.Slots.swap23 j) = pilotWeights j := by
  decide

/-- **The pilot-style weighted ledger is not label-invariant.** A concrete tuple
witnesses the failure, so the non-uniformity is not a bookkeeping artefact. -/
theorem pilotLedger_not_invariant :
    ∃ x : IUTBridge.Slots.Tuple p 4,
      weightedLedger p pilotWeights (IUTBridge.Slots.relabel p IUTBridge.Slots.swap23 x) ≠
        weightedLedger p pilotWeights x := by
  have hnot : ¬ ∀ x : IUTBridge.Slots.Tuple p 4,
      weightedLedger p pilotWeights (IUTBridge.Slots.relabel p IUTBridge.Slots.swap23 x) =
        weightedLedger p pilotWeights x :=
    (weightedLedger_invariant_iff p IUTBridge.Slots.swap23 pilotWeights).not.mpr
      pilotWeights_not_invariant
  exact not_forall.mp hnot

/-- The norm product is the exponential of the total ledger: the precise sense in
which the total ledger is a log-volume, with nonzero premises stated. -/
theorem norm_prod_eq_zpow_totalLedger {n : Nat} (x : IUTBridge.Slots.Tuple p n)
    (hx : ∀ j, x j ≠ 0) :
    (∏ j, ‖x j‖) = (p : ℝ) ^ (-(totalLedger p x)) := by
  have hprod : (∏ j, ‖x j‖) = ∏ j, (p : ℝ) ^ (-(vprofile p x j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    exact Padic.norm_eq_zpow_neg_valuation (hx j)
  rw [hprod]
  have hkey : ∀ s : Finset (Fin n),
      s.prod (fun j => (p : ℝ) ^ (-(vprofile p x j))) =
        (p : ℝ) ^ (-(s.sum (fun j => vprofile p x j))) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
          ← zpow_add₀ (IUTBridge.ScaleLedger.pR_ne_zero p)]
        congr 1
        ring
  rw [hkey Finset.univ]
  congr 1
  simp only [totalLedger, weightedLedger, one_mul]

end

end IUTBridge.WeightedLedger
