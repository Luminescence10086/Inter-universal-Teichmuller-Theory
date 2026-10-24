import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! A genuine finite compact space with individually satisfiable closed constraints
whose joint solution set is empty. Constant zero score gives each individual constraint
an exact target witness, but still gives no common witness. -/
set_option autoImplicit false
namespace CoreCompactness
open Set

local instance : TopologicalSpace Bool := ⊥

/-- Individual witnesses cannot replace the finite JOINT feasibility hypothesis,
even on a two-point compact space and with a constant continuous score. -/
theorem independent_witnesses_do_not_glue :
    CompactSpace Bool ∧
    ∃ (C : Bool → Set Bool) (L : Bool → ℝ),
      (∀ i, IsClosed (C i)) ∧ Continuous L ∧
      (∀ i, ∃ x, x ∈ C i ∧ (0 : ℝ) ≤ L x) ∧
      ¬ ∃ x, ∀ i, x ∈ C i := by
  refine ⟨inferInstance, (fun i => {i}), (fun _ => 0), ?_, continuous_const, ?_, ?_⟩
  · intro i
    exact isClosed_discrete _
  · intro i
    exact ⟨i, rfl, le_rfl⟩
  · rintro ⟨x, hx⟩
    have hfalse : x = false := hx false
    have htrue : x = true := hx true
    exact Bool.false_ne_true (hfalse.symm.trans htrue)

#print axioms independent_witnesses_do_not_glue
end CoreCompactness
