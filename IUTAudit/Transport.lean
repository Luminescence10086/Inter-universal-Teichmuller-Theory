import Std

/-!
# Source tracking and joint admissibility interfaces

This file supplies generic interfaces for indexed sources, dependent tuples,
reindexing, and coupled admissibility. An admissible pair is kept as a joint
relation; membership is never inferred merely from its two marginal projections.

No interface here has been connected to actual IUT packets, Ind1 operations,
Kummer elements, or local arithmetic data. The place/rho result is a statement
about a supplied place map and supplied function rho, without a claim that these
have been realized by an IUT construction.
-/

set_option autoImplicit false

namespace IUTAudit.Transport

universe u v w z

/-- Explicit forward and inverse maps with both inverse laws. -/
structure Reindexing (I : Type u) (J : Type v) where
  forward : I → J
  inverse : J → I
  left_inv : ∀ i : I, inverse (forward i) = i
  right_inv : ∀ j : J, forward (inverse j) = j

/-- Compose source-to-target reindexings in their application order. -/
def Reindexing.comp {I : Type u} {J : Type v} {K : Type w}
    (e : Reindexing I J) (d : Reindexing J K) : Reindexing I K where
  forward i := d.forward (e.forward i)
  inverse k := e.inverse (d.inverse k)
  left_inv i := by rw [d.left_inv, e.left_inv]
  right_inv k := by rw [e.right_inv, d.right_inv]

/-- Transport a dependent tuple to the pulled-back target fibers.
At target label `j`, the fiber is exactly `X (e.inverse j)`; no identification
between unrelated fibers is silently supplied. -/
def transport {I : Type u} {J : Type v}
    (e : Reindexing I J) (X : I → Type w) (x : (i : I) → X i) :
    (j : J) → X (e.inverse j) := fun j => x (e.inverse j)

/-- Projecting at the transported source label recovers the source component,
with the required dependent fiber cast displayed explicitly. -/
theorem transport_projection {I : Type u} {J : Type v}
    (e : Reindexing I J) (X : I → Type w) (x : (i : I) → X i) (i : I) :
    cast (congrArg X (e.left_inv i)) (transport e X x (e.forward i)) = x i := by
  have cast_apply : ∀ (a b : I) (h : a = b),
      cast (congrArg X h) (x a) = x b := by
    intro a b h
    cases h
    rfl
  exact cast_apply (e.inverse (e.forward i)) i (e.left_inv i)

/-- Composite reindexing equals successive transport, including its exact fibers. -/
theorem transport_comp {I : Type u} {J : Type v} {K : Type w}
    (e : Reindexing I J) (d : Reindexing J K)
    (X : I → Type z) (x : (i : I) → X i) :
    transport (e.comp d) X x =
      transport d (fun j => X (e.inverse j)) (transport e X x) := by
  rfl

/-- Any rho function of the transported component's place recovers its source
value at the transported source label. This tracks the component and its place
together, rather than replacing either by a distinguished target projection. -/
theorem rho_follows_place {I : Type u} {J : Type v} {P R : Type z}
    (e : Reindexing I J) (X : I → Type w) (x : (i : I) → X i)
    (place : (i : I) → X i → P) (rho : P → R) (i : I) :
    rho (place (e.inverse (e.forward i)) (transport e X x (e.forward i))) =
      rho (place i (x i)) := by
  exact congrArg (fun a => rho (place a (x a))) (e.left_inv i)

/-- Seeds may change both parameter types and the realized state type.
Realization requires a proof of the joint admissibility relation, without
assuming any desired bound on the resulting state. -/
structure SeededFamily (Seed : Type u) where
  Kappa : Seed → Type v
  Sigma : Seed → Type w
  State : Seed → Type z
  admissible : (seed : Seed) → Kappa seed → Sigma seed → Prop
  realize : (seed : Seed) → (k : Kappa seed) → (s : Sigma seed) →
    admissible seed k s → State seed

/-- The family image retains the same seed and a jointly admissible pair. -/
def familyImage {Seed : Type u} (F : SeededFamily Seed) (seed : Seed)
    (x : F.State seed) : Prop :=
  ∃ k : F.Kappa seed, ∃ s : F.Sigma seed, ∃ h : F.admissible seed k s,
    F.realize seed k s h = x

/-- Bounding the family image is exactly bounding every jointly admissible
realization at that seed. The statement does not introduce marginal choices. -/
theorem familyImage_bound_iff {Seed : Type u} (F : SeededFamily Seed)
    (seed : Seed) (B : F.State seed → Prop) :
    (∀ x : F.State seed, familyImage F seed x → B x) ↔
      (∀ (k : F.Kappa seed) (s : F.Sigma seed) (h : F.admissible seed k s),
        B (F.realize seed k s h)) := by
  constructor
  · intro hb k s h
    exact hb _ ⟨k, s, h, rfl⟩
  · intro hb x hx
    obtain ⟨k, s, h, heq⟩ := hx
    rw [← heq]
    exact hb k s h

/-- The kappa marginal records that some sigma makes the pair admissible. -/
def LeftAllowed {K : Type u} {S : Type v} (A : K → S → Prop) (k : K) : Prop :=
  ∃ s : S, A k s

/-- The sigma marginal records that some kappa makes the pair admissible. -/
def RightAllowed {K : Type u} {S : Type v} (A : K → S → Prop) (s : S) : Prop :=
  ∃ k : K, A k s

/-- The explicit cross-pair condition needed for independent marginal choices. -/
def IsRectangular {K : Type u} {S : Type v} (A : K → S → Prop) : Prop :=
  ∀ (k1 k2 : K) (s1 s2 : S), A k1 s1 → A k2 s2 → A k1 s2

/-- A joint relation equals the Cartesian product of its marginal projections
if and only if it satisfies the rectangularity condition. Thus rectangularity
is necessary as well as sufficient for replacing joint choices by independent
ones; it cannot be omitted as an implementation convention. -/
theorem rectangular_iff_product {K : Type u} {S : Type v} (A : K → S → Prop) :
    IsRectangular A ↔
      (∀ (k : K) (s : S), A k s ↔ LeftAllowed A k ∧ RightAllowed A s) := by
  constructor
  · intro hr k s
    constructor
    · intro h
      exact ⟨⟨s, h⟩, ⟨k, h⟩⟩
    · intro h
      obtain ⟨s1, h1⟩ := h.1
      obtain ⟨k2, h2⟩ := h.2
      exact hr k k2 s1 s h1 h2
  · intro hp k1 k2 s1 s2 h1 h2
    exact (hp k1 s2).2 ⟨⟨s1, h1⟩, ⟨k2, h2⟩⟩

/-- A finite coupled-choice relation: only equal Boolean choices are admissible. -/
def coupledChoice (k s : Bool) : Prop := k = s

/-- Every marginal Boolean choice is allowed, yet the particular pair
`(false, true)` is forbidden and rectangularity fails. Separate admissibility
of kappa and sigma therefore does not establish joint admissibility. -/
theorem coupled_choice_counterexample :
    (∀ k : Bool, LeftAllowed coupledChoice k) ∧
    (∀ s : Bool, RightAllowed coupledChoice s) ∧
    ¬ coupledChoice false true ∧ ¬ IsRectangular coupledChoice := by
  constructor
  · intro k
    exact ⟨k, rfl⟩
  · constructor
    · intro s
      exact ⟨s, rfl⟩
    · constructor
      · change ¬ (false = true)
        decide
      · intro hr
        have hbad := hr false true false true rfl rfl
        cases hbad

end IUTAudit.Transport
