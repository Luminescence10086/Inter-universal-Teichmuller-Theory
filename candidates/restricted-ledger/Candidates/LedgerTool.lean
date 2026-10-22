import Candidates.RestrictedLedger

/-! Finite profile domains of actual Q_p tuples; no IUT admissibility assertion. -/
set_option autoImplicit false
open scoped BigOperators
namespace Candidates.LedgerTool
noncomputable section
open Classical IUTBridge.Slots IUTBridge.WeightedLedger Candidates.RestrictedLedger
variable (p : Nat) [hp : Fact p.Prime]

def powerTuple {n : Nat} (e : Fin n → ℤ) : Tuple p n := fun j => (p : ℚ_[p]) ^ e j

theorem powerTuple_ne_zero {n : Nat} (e : Fin n → ℤ) (j : Fin n) :
    powerTuple p e j ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)

@[simp] theorem vprofile_powerTuple {n : Nat} (e : Fin n → ℤ) :
    vprofile p (powerTuple p e) = e := by
  funext j
  simp [vprofile, powerTuple, Padic.valuation_zpow]

@[simp] theorem valuation_powerTuple {n : Nat} (e : Fin n → ℤ) (j : Fin n) :
    (powerTuple p e j).valuation = e j := congrFun (vprofile_powerTuple p e) j

theorem weightedLedger_powerTuple {n : Nat} (w e : Fin n → ℤ) :
    weightedLedger p w (powerTuple p e) = dot w e := by
  change dot w (vprofile p (powerTuple p e)) = dot w e
  rw [vprofile_powerTuple]

def profileDomain {n m : Nat} (E : Fin m → Fin n → ℤ) : Set (Tuple p n) :=
  {x | (∀ j, x j ≠ 0) ∧ ∃ k, vprofile p x = E k}

theorem powerTuple_mem {n m : Nat} (E : Fin m → Fin n → ℤ) (k : Fin m) :
    powerTuple p (E k) ∈ profileDomain p E :=
  ⟨powerTuple_ne_zero p _, k, vprofile_powerTuple p _⟩

/-- The two span inclusions do not require generators to be actual differences. -/
theorem finite_criterion {n m r : Nat} (E : Fin m → Fin n → ℤ) (base : Fin m)
    (w s : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (B : Fin r → Fin n → ℤ) (G : Fin m → Fin r → ℤ) (M : Fin r → Fin m → ℤ)
    (hgen : ∀ k, E k - E base = ∑ i, G k i • B i)
    (hmem : ∀ i, B i = ∑ k, M i k • (E k - E base)) :
    (∀ x ∈ profileDomain p E,
      weightedLedger p w (relabel p σ (slotwise p (powerTuple p s) x)) =
        weightedLedger p w x) ↔
      dot (fun j => w (σ j) - w j) (E base) + ∑ j, w (σ j) * s j = 0 ∧
      ∀ i, dot (fun j => w (σ j) - w j) (B i) = 0 := by
  have hc := restricted_ledger_combination_criterion p (profileDomain p E)
    (fun _ hx => hx.1) w σ (powerTuple p s) (powerTuple_ne_zero p s)
    (powerTuple p (E base)) (powerTuple_mem p E base) B
    (fun x hx => by
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨G k, ?_⟩
      rw [hk, vprofile_powerTuple]
      exact hgen k)
    (fun i => by
      refine ⟨m, fun k => powerTuple p (E k), M i, fun k => powerTuple_mem p E k, ?_⟩
      simpa only [vprofile_powerTuple] using hmem i)
  simpa only [vprofile_powerTuple, valuation_powerTuple] using hc

theorem ledger_counterexample {n m : Nat} (E : Fin m → Fin n → ℤ) (k : Fin m)
    (w s : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (h : dot (fun j => w (σ j) - w j) (E k) + ∑ j, w (σ j) * s j ≠ 0) :
    powerTuple p (E k) ∈ profileDomain p E ∧
    weightedLedger p w (relabel p σ (slotwise p (powerTuple p s) (powerTuple p (E k)))) ≠
      weightedLedger p w (powerTuple p (E k)) := by
  refine ⟨powerTuple_mem p E k, ?_⟩
  intro heq
  have hs := weightedLedger_shift p σ w (powerTuple p s) (powerTuple p (E k))
    (powerTuple_ne_zero p s) (powerTuple_ne_zero p (E k))
  rw [heq, sub_self, vprofile_powerTuple] at hs
  exact h (by simpa only [valuation_powerTuple] using hs.symm)

def transformProfile {n : Nat} (σ : Equiv.Perm (Fin n)) (s e : Fin n → ℤ) : Fin n → ℤ :=
  fun j => s (σ.symm j) + e (σ.symm j)

theorem transform_profile {n : Nat} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (x : Tuple p n) (hx : ∀ j, x j ≠ 0) :
    vprofile p (relabel p σ (slotwise p (powerTuple p s) x)) =
      transformProfile σ s (vprofile p x) := by
  funext j
  rw [vprofile_relabel, vprofile_slotwise p _ _ _ (powerTuple_ne_zero p s _) (hx _)]
  change (vprofile p (powerTuple p s)) (σ.symm j) + _ = _
  rw [vprofile_powerTuple]
  rfl

theorem weightedLedger_transformed_powerTuple {n : Nat} (w s e : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    weightedLedger p w (relabel p σ (slotwise p (powerTuple p s) (powerTuple p e))) =
      dot w (transformProfile σ s e) := by
  change dot w (vprofile p (relabel p σ (slotwise p (powerTuple p s) (powerTuple p e)))) = _
  rw [transform_profile p σ s _ (powerTuple_ne_zero p e), vprofile_powerTuple]

/-- Domain closure is an obligation separate from preservation of the ledger. -/
theorem domain_invariant_iff {n m : Nat} (E : Fin m → Fin n → ℤ)
    (s : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (∀ x ∈ profileDomain p E, relabel p σ (slotwise p (powerTuple p s) x) ∈ profileDomain p E) ↔
    ∀ k, ∃ l, transformProfile σ s (E k) = E l := by
  constructor
  · intro h k
    obtain ⟨l, hl⟩ := (h _ (powerTuple_mem p E k)).2
    refine ⟨l, ?_⟩
    simpa only [transform_profile p σ s _ (powerTuple_ne_zero p _), vprofile_powerTuple] using hl
  · intro h x hx
    refine ⟨fun j => mul_ne_zero (powerTuple_ne_zero p s _) (hx.1 _), ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    obtain ⟨l, hl⟩ := h k
    exact ⟨l, by rw [transform_profile p σ s x hx.1, hk, hl]⟩

theorem domain_counterexample {n m : Nat} (E : Fin m → Fin n → ℤ)
    (s : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (k : Fin m)
    (h : ∀ l, transformProfile σ s (E k) ≠ E l) :
    powerTuple p (E k) ∈ profileDomain p E ∧
      relabel p σ (slotwise p (powerTuple p s) (powerTuple p (E k))) ∉ profileDomain p E := by
  refine ⟨powerTuple_mem p E k, ?_⟩
  intro hx
  obtain ⟨l, hl⟩ := hx.2
  apply h l
  simpa only [transform_profile p σ s _ (powerTuple_ne_zero p _), vprofile_powerTuple] using hl

end
end Candidates.LedgerTool
