import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Abstract sufficient criterion only. Finite JOINT near-feasibility is an explicit
hypothesis. This file supplies neither IUT constraints nor a proof of that hypothesis. -/
set_option autoImplicit false
namespace CoreCompactness
open Set

variable {X I : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Finite joint near-feasibility reaches the threshold without epsilon loss for each finite family. -/
theorem finite_joint_threshold_of_near_feasible
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) (L : X → ℝ)
    (hL : UpperSemicontinuous L) (a : ℝ)
    (hjoint : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : X, (∀ i ∈ s, x ∈ C i) ∧ a - ε ≤ L x)
    (s : Finset I) : ∃ x : X, (∀ i ∈ s, x ∈ C i) ∧ a ≤ L x := by
  let S : Set X := ⋂ i ∈ s, C i
  have hS : IsClosed S := isClosed_biInter (fun i _ => hC i)
  obtain ⟨y, hy, _⟩ := hjoint s 1 (by norm_num)
  have hSne : S.Nonempty := ⟨y, by simpa [S] using hy⟩
  obtain ⟨x, hx, hmax⟩ := (hL.upperSemicontinuousOn S).exists_isMaxOn hSne hS.isCompact
  refine ⟨x, by simpa [S] using hx, ?_⟩
  by_contra h
  have hgap : 0 < (a - L x) / 2 := by linarith
  obtain ⟨z, hz, hnear⟩ := hjoint s ((a - L x) / 2) hgap
  have hzS : z ∈ S := by simpa [S] using hz
  have hzmax : L z ≤ L x := hmax hzS
  linarith

/-- Compactness glues finite jointly chosen near-solutions into ONE global solution with score at least the threshold. -/
theorem exists_joint_threshold_of_compact
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) (L : X → ℝ)
    (hL : UpperSemicontinuous L) (a : ℝ)
    (hjoint : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : X, (∀ i ∈ s, x ∈ C i) ∧ a - ε ≤ L x) :
    ∃ x : X, (∀ i, x ∈ C i) ∧ a ≤ L x := by
  have hfinite : ∀ s : Finset I, ((L ⁻¹' Ici a) ∩ ⋂ i ∈ s, C i).Nonempty := by
    intro s
    obtain ⟨x, hx, hscore⟩ := finite_joint_threshold_of_near_feasible C hC L hL a hjoint s
    exact ⟨x, hscore, by simpa using hx⟩
  obtain ⟨x, hscore, hx⟩ :=
    (hL.isClosed_preimage a).isCompact.inter_iInter_nonempty C hC hfinite
  exact ⟨x, by simpa using hx, hscore⟩

/-- An upper bound on the SAME global feasible points implies the numerical bound. -/
theorem bound_of_joint_near_feasible
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) (L : X → ℝ)
    (hL : UpperSemicontinuous L) (a b : ℝ)
    (hjoint : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : X, (∀ i ∈ s, x ∈ C i) ∧ a - ε ≤ L x)
    (hupper : ∀ x : X, (∀ i, x ∈ C i) → L x ≤ b) : a ≤ b := by
  obtain ⟨x, hx, hax⟩ := exists_joint_threshold_of_compact C hC L hL a hjoint
  exact hax.trans (hupper x hx)

/-- The continuous-score specialization of the upper-semicontinuous criterion. -/
theorem exists_joint_threshold_of_continuous
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) (L : X → ℝ)
    (hL : Continuous L) (a : ℝ)
    (hjoint : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : X, (∀ i ∈ s, x ∈ C i) ∧ a - ε ≤ L x) :
    ∃ x : X, (∀ i, x ∈ C i) ∧ a ≤ L x :=
  exists_joint_threshold_of_compact C hC L hL.upperSemicontinuous a hjoint

#print axioms finite_joint_threshold_of_near_feasible
#print axioms exists_joint_threshold_of_compact
#print axioms bound_of_joint_near_feasible
#print axioms exists_joint_threshold_of_continuous
end CoreCompactness

