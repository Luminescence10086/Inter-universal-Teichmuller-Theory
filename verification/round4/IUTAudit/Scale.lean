import Std

/-!
Generic natural-number models for normalization and comparison audits.
These statements neither encode IUT III Corollary 3.12 nor refute it.
Natural numbers here are a discrete test bed, not Arakelov log-volumes.
-/

namespace IUTAudit.Scale

/-- A deliberately explicit choice of scale. -/
def scaled (k x : Nat) : Nat := k * x

/-- A change of scale composes multiplicatively. -/
theorem scale_composition (k l x : Nat) :
    scaled k (scaled l x) = scaled (k * l) x := by
  exact (Nat.mul_assoc k l x).symm

/-- Fixing the value on the unit forces the scale to be one. -/
theorem normalization_at_unit (k : Nat) (h : scaled k 1 = 1) : k = 1 := by
  simpa [scaled] using h

/-- A unit normalization suffices for preservation of all measurements. -/
theorem normalized_scale_preserves (k : Nat) (h : scaled k 1 = 1) (x : Nat) :
    scaled k x = x := by
  rw [normalization_at_unit k h]
  simp [scaled]

/-- Unrestricted scales have no uniform bound, even at one test point. -/
theorem no_uniform_bound : ¬ ∃ B : Nat, ∀ k : Nat, scaled k 1 ≤ B := by
  intro ⟨B, h⟩
  have hb := h (B + 1)
  simp only [scaled, Nat.mul_one] at hb
  omega

/-- A concrete rescaling cannot silently be replaced by the identity. -/
theorem scale_two_not_identity : scaled 2 1 ≠ 1 := by
  decide

/-- Discrete algebraic test with averages 3/2 and 5/2, clearing denominators.
No identification of d or q with any IUT object is asserted. -/
theorem weighted_comparison_forces_bound (d q : Int)
    (h : -2 * q ≤ 3 * d - 5 * q) : q ≤ d := by
  omega

/-- Removing the differing coefficient eliminates all dependence on q. -/
theorem erased_comparison_iff (d q : Int) :
    (-2 * q ≤ 3 * d - 2 * q) ↔ 0 ≤ d := by
  omega

/-- The erased comparison allows unbounded q even for a fixed nonnegative d. -/
theorem erased_comparison_unbounded (d : Int) (hd : 0 ≤ d) (B : Int) :
    ∃ q : Int, B < q ∧ -2 * q ≤ 3 * d - 2 * q := by
  refine ⟨B + 1, ?_, ?_⟩
  · omega
  · exact (erased_comparison_iff d (B + 1)).2 hd

end IUTAudit.Scale
