import IUTBridge.WeightedLedger
import IUTBridge.Admissibility

/-!
# Combined permutation and scaling bookkeeping on finite p-adic tuples

This module packages the diagonal commutation criterion and computes the exact
weighted valuation ledger of scaling followed by relabelling. On tuples whose
every coordinate is nonzero, preservation for every tuple is equivalent to
invariant weights together with zero weighted valuation budget. The converse is
tested by the constant-one tuple and the existing delta tuples; none of these
tests needs an assumption that the slot set is nonempty.

Mathlib assigns valuation zero to the zero element. The final support-sensitive
formula therefore records only the scaling budget at nonzero coordinates.
In particular, a zero total budget alone must not be applied to arbitrary tuples.

These are elementary statements about actual `Q_p` and arbitrary integer
weights on abstract finite slots. They construct no IUT object, measure,
Arakelov volume, abc estimate, or claim of mathematical novelty.
-/

set_option autoImplicit false

open scoped BigOperators

namespace IUTBridge.Integration

noncomputable section

open Classical IUTBridge.Slots IUTBridge.WeightedLedger

variable (p : Nat) [hp : Fact p.Prime]

/-- A diagonal action commutes with relabelling on every tuple exactly when its
scalar family is invariant. There are no nonzero premises for this criterion. -/
theorem slotwise_commutes_iff {n : Nat} (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) :
    (∀ x : Tuple p n,
      relabel p σ (slotwise p a x) = slotwise p a (relabel p σ x)) ↔
      ∀ j : Fin n, a (σ.symm j) = a j := by
  constructor
  · intro h j
    have hj := congrFun (h (fun _ => 1)) j
    simpa only [relabel, slotwise, mul_one] using hj
  · intro h x
    exact slotwise_commutes_of_invariant p σ a h x

/-- The delta probes used to recover individual weights have no zero
coordinates, including at slots other than the distinguished one. -/
theorem deltaTuple_ne_zero {n : Nat} (i j : Fin n) :
    deltaTuple p i j ≠ 0 := by
  exact zpow_ne_zero _ (IUTBridge.ScaleLedger.p_ne_zero p)

/-- Scaling first and relabelling second transports both the weights on the
input tuple and the weights on the scalar valuation budget. -/
theorem weightedLedger_relabel_slotwise {n : Nat}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (x : Tuple p n) (ha : ∀ j, a j ≠ 0) (hx : ∀ j, x j ≠ 0) :
    weightedLedger p w (relabel p σ (slotwise p a x)) =
      weightedLedger p (fun j => w (σ j)) x +
        ∑ j, w (σ j) * (a j).valuation := by
  rw [weightedLedger_relabel]
  change weightedLedger p (fun j => w (σ j)) (slotwise p a x) = _
  exact weightedLedger_slotwise p _ a x ha hx

/-- On the coordinatewise nonzero locus, a fixed combined action preserves the
weighted ledger on every tuple iff the weights are permutation-invariant and
the weighted scaling budget vanishes. Nonzero scalars are an explicit premise;
nonzero input coordinates are part of the quantified preservation property. -/
theorem weightedLedger_combined_invariant_iff {n : Nat}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (ha : ∀ j, a j ≠ 0) :
    (∀ x : Tuple p n, (∀ j, x j ≠ 0) →
      weightedLedger p w (relabel p σ (slotwise p a x)) =
        weightedLedger p w x) ↔
      (∀ j, w (σ j) = w j) ∧ (∑ j, w j * (a j).valuation) = 0 := by
  constructor
  · intro h
    have hbudget : (∑ j, w (σ j) * (a j).valuation) = 0 := by
      have hone := h (fun _ => 1) (fun _ => one_ne_zero)
      rw [weightedLedger_relabel_slotwise p σ w a _ ha
        (fun _ => one_ne_zero)] at hone
      simpa [weightedLedger, vprofile] using hone
    have hw : ∀ j, w (σ j) = w j := by
      intro j
      have hdelta := h (deltaTuple p j) (deltaTuple_ne_zero p j)
      rw [weightedLedger_relabel_slotwise p σ w a _ ha
        (deltaTuple_ne_zero p j), hbudget, add_zero,
        weightedLedger_delta, weightedLedger_delta] at hdelta
      exact hdelta
    refine ⟨hw, ?_⟩
    simpa only [hw] using hbudget
  · rintro ⟨hw, hbudget⟩ x hx
    rw [weightedLedger_relabel_slotwise p σ w a x ha hx]
    simp only [hw, hbudget, add_zero]

/-- If the weights fail invariance or the scaling budget is nonzero, there is a
coordinatewise nonzero tuple witnessing failure of ledger preservation. -/
theorem exists_combined_ledger_failure {n : Nat}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (ha : ∀ j, a j ≠ 0)
    (hfailure : (∃ j, w (σ j) ≠ w j) ∨ (∑ j, w j * (a j).valuation) ≠ 0) :
    ∃ x : Tuple p n, (∀ j, x j ≠ 0) ∧
      weightedLedger p w (relabel p σ (slotwise p a x)) ≠
        weightedLedger p w x := by
  classical
  by_contra h
  have hinvariant : ∀ x : Tuple p n, (∀ j, x j ≠ 0) →
      weightedLedger p w (relabel p σ (slotwise p a x)) =
        weightedLedger p w x := by
    intro x hx
    by_contra hne
    exact h ⟨x, hx, hne⟩
  obtain ⟨hw, hb⟩ :=
    (weightedLedger_combined_invariant_iff p σ w a ha).mp hinvariant
  rcases hfailure with ⟨j, hj⟩ | hb'
  · exact hj (hw j)
  · exact hb' hb

/-- For arbitrary input tuples, the budget is supported precisely on their
nonzero coordinates. This formula explicitly handles valuation at zero. -/
theorem weightedLedger_relabel_slotwise_support {n : Nat}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (x : Tuple p n) (ha : ∀ j, a j ≠ 0) :
    weightedLedger p w (relabel p σ (slotwise p a x)) =
      weightedLedger p (fun j => w (σ j)) x +
        ∑ j, if x j = 0 then 0 else w (σ j) * (a j).valuation := by
  classical
  rw [weightedLedger_relabel]
  unfold weightedLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : x j = 0
  · simp [vprofile, slotwise, hx]
  · rw [vprofile_slotwise p a x j (ha j) hx]
    simp only [hx, ↓reduceIte]
    ring

/-- If preservation is required on all tuples, including tuples with zero
coordinates, cancellation between different scalar budgets is insufficient.
Each weighted scalar valuation must vanish separately. -/
theorem weightedLedger_combined_invariant_all_iff {n : Nat}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → Int) (a : Fin n → ℚ_[p])
    (ha : ∀ j, a j ≠ 0) :
    (∀ x : Tuple p n,
      weightedLedger p w (relabel p σ (slotwise p a x)) =
        weightedLedger p w x) ↔
      (∀ j, w (σ j) = w j) ∧ (∀ j, w j * (a j).valuation = 0) := by
  constructor
  · intro h
    have hw : ∀ j, w (σ j) = w j :=
      ((weightedLedger_combined_invariant_iff p σ w a ha).mp (fun x _ => h x)).1
    refine ⟨hw, ?_⟩
    intro j
    have hj := h (fun i => if i = j then 1 else 0)
    rw [weightedLedger_relabel_slotwise_support p σ w a _ ha] at hj
    simpa [weightedLedger, vprofile, apply_ite, hw] using hj
  · rintro ⟨hw, hb⟩ x
    rw [weightedLedger_relabel_slotwise_support p σ w a x ha]
    simp only [hw, hb, ite_self, Finset.sum_const_zero, add_zero]

/-- The marginal of the relation with target layer frozen at `c` consists
exactly of `c`, including an explicit witness for the reverse implication. -/
theorem frozen_sigma_marginal_iff (c k : Int) :
    IUTBridge.Admissibility.RightAllowed
      (fun (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (m : Int) =>
        IUTBridge.Admissibility.LatticeAdmissible p e m ∧ m = c) k ↔ k = c := by
  constructor
  · rintro ⟨e, _, hk⟩
    exact hk
  · intro hk
    subst k
    exact ⟨IUTBridge.ScaleLedger.shift p c,
      IUTBridge.Admissibility.latticeAdmissible_attained p c, rfl⟩

/-- A nonempty rectangular subrelation of lattice admissibility realizes
exactly one layer. Nonemptiness is essential to the existence part; the
underlying at-most-one-layer theorem alone also applies to empty relations. -/
theorem rectangular_nonempty_unique_layer
    (R : (ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) → Int → Prop)
    (hsub : ∀ (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int),
      R e k → IUTBridge.Admissibility.LatticeAdmissible p e k)
    (hrect : IUTBridge.Admissibility.IsRectangular R)
    (hne : ∃ (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int), R e k) :
    ∃! k : Int, IUTBridge.Admissibility.RightAllowed R k := by
  obtain ⟨e₀, k₀, h₀⟩ := hne
  refine ⟨k₀, ⟨e₀, h₀⟩, ?_⟩
  rintro k ⟨e, he⟩
  exact IUTBridge.Admissibility.rectangular_subrelation_freezes_layer
    p R hsub hrect he h₀

end

end IUTBridge.Integration
