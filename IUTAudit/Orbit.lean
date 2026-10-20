import Std

/-!
# An abstract envelope under allowed operations

Regions are predicates. The union of the images under a family of operations
need not be stable under further operations. Explicit composition closure makes
it stable, and an explicit identity witness makes it cover the original region.
Under both hypotheses it is an idempotent closure construction.

These are generic set/action mechanisms. No IUT object, indeterminacy, or
arithmetic bound is modeled here. In particular no instance for IUT's Ind1 has
been established. A correspondence with such an instance would require further
definitions and independently checked proofs.
-/

set_option autoImplicit false

namespace IUTAudit.Orbit

universe u v

/-- The union of all allowed images of a region. -/
def unionOfImages {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop) (x : X) : Prop :=
  ∃ i : I, ∃ y : X, U y ∧ T i y = x

/-- The image envelope; orbit stability is proved only under explicit hypotheses. -/
abbrev orbitEnvelope {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop) : X → Prop := unionOfImages T U

/-- Forward stability: every allowed operation preserves region membership. -/
def IsClosed {I : Type u} {X : Type v}
    (T : I → X → X) (V : X → Prop) : Prop :=
  ∀ i : I, ∀ x : X, V x → V (T i x)

/-- The allowed operations include an explicitly witnessed identity. -/
def HasIdentity {I : Type u} {X : Type v} (T : I → X → X) : Prop :=
  ∃ e : I, ∀ x : X, T e x = x

/-- Every composite of two allowed operations has an allowed representative. -/
def CompositionClosed {I : Type u} {X : Type v} (T : I → X → X) : Prop :=
  ∀ i j : I, ∃ k : I, ∀ x : X, T i (T j x) = T k x

/-- Each point in each allowed image belongs to the envelope. -/
theorem image_mem_envelope {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop) (i : I) (x : X) (hx : U x) :
    orbitEnvelope T U (T i x) := by
  exact ⟨i, x, hx, rfl⟩

/-- An identity witness ensures that the envelope covers its source region. -/
theorem envelope_covers {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop) (hid : HasIdentity T) :
    ∀ x : X, U x → orbitEnvelope T U x := by
  obtain ⟨e, he⟩ := hid
  intro x hx
  exact ⟨e, x, hx, he x⟩

/-- Every bound containing all allowed images also contains their envelope. -/
theorem envelope_minimal {I : Type u} {X : Type v}
    (T : I → X → X) (U V : X → Prop)
    (himages : ∀ i : I, ∀ x : X, U x → V (T i x)) :
    ∀ x : X, orbitEnvelope T U x → V x := by
  intro x hx
  obtain ⟨i, y, hy, heq⟩ := hx
  rw [← heq]
  exact himages i y hy

/-- A stable bound containing the source automatically contains the envelope. -/
theorem envelope_minimal_closed {I : Type u} {X : Type v}
    (T : I → X → X) (U V : X → Prop)
    (hclosed : IsClosed T V) (hUV : ∀ x : X, U x → V x) :
    ∀ x : X, orbitEnvelope T U x → V x := by
  apply envelope_minimal T U V
  intro i x hx
  exact hclosed i x (hUV x hx)

/-- Composition closure, without an identity assumption, makes the envelope stable. -/
theorem envelope_closed {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop) (hcomp : CompositionClosed T) :
    IsClosed T (orbitEnvelope T U) := by
  intro i x hx
  obtain ⟨j, y, hy, hj⟩ := hx
  obtain ⟨k, hk⟩ := hcomp i j
  refine ⟨k, y, hy, ?_⟩
  rw [← hk y, hj]

/-- With identity and composition witnesses, a second envelope adds no points. -/
theorem envelope_idempotent {I : Type u} {X : Type v}
    (T : I → X → X) (U : X → Prop)
    (hid : HasIdentity T) (hcomp : CompositionClosed T) :
    ∀ x : X, orbitEnvelope T (orbitEnvelope T U) x ↔ orbitEnvelope T U x := by
  intro x
  constructor
  · exact envelope_minimal_closed T (orbitEnvelope T U) (orbitEnvelope T U)
      (envelope_closed T U hcomp) (fun _ hx => hx) x
  · exact envelope_covers T (orbitEnvelope T U) hid x

/-- Two allowed operations on two labels: identity and label exchange. -/
def swapAction (i x : Bool) : Bool := if i then !x else x

/-- A bound that singles out one label. -/
def fixedLabel (x : Bool) : Prop := x = false

/-- The two operations have explicit identity and composition witnesses. -/
theorem swapAction_witnesses : HasIdentity swapAction ∧ CompositionClosed swapAction := by
  constructor
  · exact ⟨false, fun _ => rfl⟩
  · intro i j
    refine ⟨i != j, ?_⟩
    intro x
    cases i <;> cases j <;> cases x <;> rfl

/-- A bound on a fixed label is not preserved by the allowed label exchange. -/
theorem fixedLabel_not_closed : ¬ IsClosed swapAction fixedLabel := by
  intro h
  have hbad := h true false rfl
  change true = false at hbad
  cases hbad

/-- The symmetric envelope of that fixed-label bound contains both labels. -/
theorem fixedLabel_envelope_full : ∀ x : Bool, orbitEnvelope swapAction fixedLabel x := by
  intro x
  refine ⟨x, false, rfl, ?_⟩
  cases x <;> rfl

/-- In the explicit two-label model, taking the envelope repairs stability. -/
theorem fixedLabel_envelope_closed : IsClosed swapAction (orbitEnvelope swapAction fixedLabel) := by
  exact envelope_closed swapAction fixedLabel swapAction_witnesses.2

end IUTAudit.Orbit
