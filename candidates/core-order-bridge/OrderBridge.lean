import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Order-level sufficient criterion only. No IUT output family is constructed here.
The outer approximation index is dependent on the *same* allowed witness.
EReal retains both infinite boundary cases instead of totalizing real infima.
-/

set_option autoImplicit false

namespace CoreOrderBridge

/-- An infimum lower bound must hold for every outer approximant. -/
theorem outer_lower_iff {I : Type*} (outer : I → EReal) (q : EReal) :
    q ≤ iInf outer ↔ ∀ i, q ≤ outer i :=
  le_iInf_iff

/-- Conditional scalar bridge: one allowed witness per epsilon, all its outer
approximants simultaneously, and an independently justified output upper bound.
Neither coverage nor the upper bound is proved for IUT by this theorem. -/
theorem inequality_of_outer_coverage {W : Type*} {A : W → Type*}
    (outer : (w : W) → A w → EReal) (allowed : W → Prop) (q b : ℝ)
    (hupper : ∀ w, allowed w → iInf (outer w) ≤ (b : EReal))
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ w, allowed w ∧
      ∀ i : A w, ((q - ε : ℝ) : EReal) ≤ outer w i) : q ≤ b := by
  by_contra h
  have hbq : b < q := lt_of_not_ge h
  obtain ⟨w, hw, happrox⟩ := hcover ((q - b) / 2) (by linarith)
  have hlow : (((q - (q - b) / 2 : ℝ)) : EReal) ≤ iInf (outer w) :=
    le_iInf happrox
  have hreal : q - (q - b) / 2 ≤ b :=
    EReal.coe_le_coe_iff.mp (hlow.trans (hupper w hw))
  linarith

/-- A single large outer approximant does not bound the infimum below.
This is an order-quantifier regression, not a counterexample to IUT. -/
theorem some_outer_is_insufficient :
    (∃ i : Bool, (1 : EReal) ≤ (if i then 1 else 0)) ∧
      ¬ (1 : EReal) ≤ ⨅ i : Bool, (if i then 1 else 0 : EReal) := by
  constructor
  · exact ⟨true, by norm_num⟩
  · intro h
    have hz : (1 : EReal) ≤ 0 := h.trans (iInf_le _ false)
    have hz' : (1 : ℝ) ≤ 0 := EReal.coe_le_coe_iff.mp hz
    norm_num at hz'

end CoreOrderBridge

#print axioms CoreOrderBridge.outer_lower_iff
#print axioms CoreOrderBridge.inequality_of_outer_coverage
#print axioms CoreOrderBridge.some_outer_is_insufficient
