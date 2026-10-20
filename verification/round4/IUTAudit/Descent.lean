import Std

/-!
# A minimal audit model for loss of information

These results concern arbitrary functions and natural-number-valued quantities.
They do not identify any object, map, or indeterminacy in IUT, and are neither
a formalization nor a refutation of IUT. Applying them to a mathematical theory
requires separately formalized definitions and proofs connecting that theory to
the hypotheses below.

The constructive sufficient condition uses an explicitly supplied section; it
does not assert that every map has a section.
-/

set_option autoImplicit false

namespace IUTAudit.Descent

universe u v

/-- A quantity has equal values at points forgotten by the same map. -/
def FiberInvariant {X : Type u} {Y : Type v} (f : X → Y) (q : X → Nat) : Prop :=
  ∀ x x' : X, f x = f x' → q x = q x'

/-- A quantity can be recovered as a function of the retained information. -/
def Descends {X : Type u} {Y : Type v} (f : X → Y) (q : X → Nat) : Prop :=
  ∃ r : Y → Nat, ∀ x : X, r (f x) = q x

/-- Descent necessarily preserves equality on each fiber. -/
theorem invariant_of_descends {X : Type u} {Y : Type v}
    (f : X → Y) (q : X → Nat) (h : Descends f q) : FiberInvariant f q := by
  obtain ⟨r, hr⟩ := h
  intro x x' hxx'
  rw [← hr x, ← hr x', hxx']

/-- An explicit section constructs descent of every fiber-invariant quantity. -/
theorem descends_of_section {X : Type u} {Y : Type v}
    (f : X → Y) (q : X → Nat) (s : Y → X)
    (hs : ∀ y : Y, f (s y) = y) (h : FiberInvariant f q) : Descends f q := by
  refine ⟨fun y => q (s y), ?_⟩
  intro x
  exact h (s (f x)) x (hs (f x))

/-- For a map with a supplied section, fiber invariance exactly characterizes descent. -/
theorem descends_iff_invariant_of_section {X : Type u} {Y : Type v}
    (f : X → Y) (q : X → Nat) (s : Y → X)
    (hs : ∀ y : Y, f (s y) = y) : Descends f q ↔ FiberInvariant f q := by
  exact ⟨invariant_of_descends f q, descends_of_section f q s hs⟩

/-- A generic counterexample: forgetting a Boolean loses its nonconstant quantity.
This is an example about `Bool → Unit`, without an asserted connection to IUT.
-/
theorem boolean_quantity_does_not_descend :
    ¬ Descends (fun _ : Bool => ()) (fun b : Bool => if b then 1 else 0) := by
  intro h
  have hi := invariant_of_descends (fun _ : Bool => ())
    (fun b : Bool => if b then 1 else 0) h
  have hbad := hi false true rfl
  simp at hbad

end IUTAudit.Descent
