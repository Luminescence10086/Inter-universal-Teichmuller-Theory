import IUTBridge.ScaleLedger

/-!
# Admissibility on actual p-adic lattices, and where marginal reasoning fails

The main project's `IUTAudit.Transport` proves, for an *abstract* joint relation,
that separate admissibility of `κ` and of `σ` cannot be replaced by independent
choice unless the relation is rectangular. Its concrete witness is a two-point
Boolean toy. This module moves that obstruction onto **actual arithmetic data**.

The joint relation is `LatticeAdmissible p e k`: the actual `Q_p`-linear
automorphism `e` sends the actual unit ball onto the actual integer layer
`layer p k`. Three facts are proved:

* every automorphism admits exactly one layer (`existsUnique_layer_of_auto` in
  `ScaleLedger`) — the joint relation is a **graph**, not a product;
* every layer is attained, and every automorphism has some layer — so both
  **marginals are total**;
* therefore the relation is **not rectangular**, and separate marginal
  admissibility does not produce a joint witness.

The contrast is made precise as well: freezing the layer makes the relation
rectangular. Fixing the layer at `0` is one such choice, and `frozen_isRectangular`
proves that **any** fixed integer `c` works equally — so the necessary condition is
"at most one layer is realised", not "the layer is `0`". What destroys the product
structure is the freedom to realise several layers at once.

Scope. `layer` is a set of p-adic numbers, never a `Q_p`-subspace, and `e` ranges
over `Q_p`-linear automorphisms of the base field, not over any Ism group. No
Ism/Kummer element, packet, seed, region membership, log-image identity or
Arakelov volume is constructed, and no conclusion is drawn about Corollary 3.12,
about the Step (v) objection, or about abc.
-/

set_option autoImplicit false

open scoped Pointwise

namespace IUTBridge.Admissibility

universe u v

/-! ## The vendored abstract interface

The definitions below are copied, character for character in their bodies, from
`IUTAudit/Transport.lean` (the `rectangularity` block there). They are duplicated
rather than imported because the two projects are separate Lean toolchains; the
repository's bridge auditor checks that the marked block text and the elaborated
statement of `rectangular_iff_product` agree in both projects. -/

-- BRIDGE-INTERFACE-BEGIN rectangularity
/-- The kappa marginal records that some sigma makes the pair admissible. -/
def LeftAllowed {K : Type u} {S : Type v} (A : K → S → Prop) (k : K) : Prop :=
  ∃ s : S, A k s

/-- The sigma marginal records that some kappa makes the pair admissible. -/
def RightAllowed {K : Type u} {S : Type v} (A : K → S → Prop) (s : S) : Prop :=
  ∃ k : K, A k s

/-- The explicit cross-pair condition needed for independent marginal choices. -/
def IsRectangular {K : Type u} {S : Type v} (A : K → S → Prop) : Prop :=
  ∀ (k1 k2 : K) (s1 s2 : S), A k1 s1 → A k2 s2 → A k1 s2
-- BRIDGE-INTERFACE-END rectangularity

/-- Vendored restatement of `IUTAudit.Transport.rectangular_iff_product`, proved
independently in this toolchain so that the bridge carries a checkable duplicate
of the abstract equivalence rather than a citation of it. -/
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

/-! ## A general graph obstruction

The Boolean example of the main project is an instance of a structural fact:
whenever the joint relation is a graph (each `κ` has a *unique* admissible `σ`)
and two different `σ` values actually occur, rectangularity necessarily fails.
This lemma is the transferable kernel; the p-adic section below instantiates it.
-/

/-- **Graph obstruction.** A joint relation that is a graph cannot be replaced by
its two marginals, as soon as two distinct values occur. -/
theorem not_rectangular_of_graph {K : Type u} {S : Type v} {A : K → S → Prop}
    (hun : ∀ (k : K) (s s' : S), A k s → A k s' → s = s')
    {k1 k2 : K} {s1 s2 : S} (h1 : A k1 s1) (h2 : A k2 s2) (hne : s1 ≠ s2) :
    ¬ IsRectangular A := by
  intro hr
  exact hne (hun k1 s1 s2 h1 (hr k1 k2 s1 s2 h1 h2))

/-- **Merginals are insufficient for a graph.** Both marginals are inhabited and
the joint relation still fails rectangularity, so the two marginal checks cannot
be composed into a joint one. -/
theorem marginals_insufficient_of_graph {K : Type u} {S : Type v} {A : K → S → Prop}
    (hun : ∀ (k : K) (s s' : S), A k s → A k s' → s = s')
    (hleft : ∀ k : K, LeftAllowed A k) (hright : ∀ s : S, RightAllowed A s)
    {k1 k2 : K} {s1 s2 : S} (h1 : A k1 s1) (h2 : A k2 s2) (hne : s1 ≠ s2) :
    (∀ k : K, LeftAllowed A k) ∧ (∀ s : S, RightAllowed A s) ∧ ¬ IsRectangular A :=
  ⟨hleft, hright, not_rectangular_of_graph hun h1 h2 hne⟩

/-! ## The actual p-adic instantiation -/

noncomputable section

variable (p : Nat) [hp : Fact p.Prime]

/-- Joint lattice admissibility on actual `Q_p`: the automorphism carries the
actual unit ball onto the integer layer `k`. Both components are genuine
arithmetic data; the relation is not a product of two independent predicates. -/
def LatticeAdmissible (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int) : Prop :=
  e '' LocalFieldAudit.Filtration.ball p = ScaleLedger.layer p k

/-- The joint relation is a graph: at each automorphism at most one layer is
admissible. -/
theorem latticeAdmissible_unique (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) {k m : Int}
    (hk : LatticeAdmissible p e k) (hm : LatticeAdmissible p e m) : k = m := by
  exact ScaleLedger.layer_injective p (hk.symm.trans hm)

/-- Every layer is attained, by the actual rescaling automorphism. -/
theorem latticeAdmissible_attained (k : Int) :
    LatticeAdmissible p (ScaleLedger.shift p k) k := by
  rw [LatticeAdmissible, ScaleLedger.image_ball_eq_layer, ScaleLedger.shift_apply,
    mul_one, Padic.valuation_zpow, Padic.valuation_p, mul_one]

/-- The identity realizes the layer of index zero. -/
theorem latticeAdmissible_refl : LatticeAdmissible p (LinearEquiv.refl ℚ_[p] ℚ_[p]) 0 := by
  rw [LatticeAdmissible, ScaleLedger.image_ball_eq_layer]
  simp

/-- **Both marginals are total on actual arithmetic data.** -/
theorem marginals_total :
    (∀ e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p], LeftAllowed (LatticeAdmissible p) e) ∧
      (∀ k : Int, RightAllowed (LatticeAdmissible p) k) := by
  constructor
  · intro e
    obtain ⟨k, hk, -⟩ := ScaleLedger.existsUnique_layer_of_auto p e
    exact ⟨k, hk⟩
  · intro k
    exact ⟨ScaleLedger.shift p k, latticeAdmissible_attained p k⟩

/-- **The actual p-adic joint relation is not rectangular.** The identity sits on
layer `0`, the actual rescaling by `p` sits on layer `1`, and no automorphism sits
on two different layers; hence the cross-pair is impossible. -/
theorem latticeAdmissible_not_rectangular :
    ¬ IsRectangular (LatticeAdmissible p) := by
  refine not_rectangular_of_graph (fun e k m hk hm => latticeAdmissible_unique p e hk hm)
    (latticeAdmissible_refl p) (latticeAdmissible_attained p 1) (by decide)

/-- **Merginal admissibility does not produce a joint witness, on actual `Q_p`.**
This is the arithmetic counterpart of `IUTAudit.Transport.coupled_choice_counterexample`:
both marginal checks pass, yet independent choice of the two components is
explicitly false, because the admissible pairs form a graph over an infinite
ladder rather than a product. -/
theorem marginals_do_not_force_joint :
    (∀ e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p], LeftAllowed (LatticeAdmissible p) e) ∧
      (∀ k : Int, RightAllowed (LatticeAdmissible p) k) ∧
        ¬ IsRectangular (LatticeAdmissible p) :=
  ⟨(marginals_total p).1, (marginals_total p).2, latticeAdmissible_not_rectangular p⟩

/-- **Where marginal reasoning is legitimate.** On the sub-relation that freezes the
layer at `0`, rectangularity holds. Freezing the lattice direction is what makes
independent choice sound; `0` here is a choice, not the only possible one (see
`frozen_isRectangular`). -/
theorem normalised_isRectangular :
    IsRectangular (fun (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int) =>
      LatticeAdmissible p e k ∧ k = 0) := by
  intro e1 e2 k1 k2 h1 h2
  obtain ⟨h1A, h1k⟩ := h1
  obtain ⟨-, h2k⟩ := h2
  exact ⟨(h1k.trans h2k.symm) ▸ h1A, h2k⟩

/-- **Any fixed layer is rectangular.** Freezing the ladder at an arbitrary integer
`c` — not only at `0` — also makes independent marginal reasoning sound. The
necessary condition is therefore "at most one layer is realised", and the choice of
which layer is free. -/
theorem frozen_isRectangular (c : Int) :
    IsRectangular (fun (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int) =>
      LatticeAdmissible p e k ∧ k = c) := by
  intro e1 e2 k1 k2 h1 h2
  obtain ⟨h1A, h1k⟩ := h1
  obtain ⟨-, h2k⟩ := h2
  exact ⟨(h1k.trans h2k.symm) ▸ h1A, h2k⟩

/-- The frozen relation at `c` has an admissible witness at `c`.
`Integration.frozen_sigma_marginal_iff` gives the full singleton characterization. -/
theorem frozen_sigma_marginal (c : Int) :
    RightAllowed (fun (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int) =>
      LatticeAdmissible p e k ∧ k = c) c :=
  ⟨IUTBridge.ScaleLedger.shift p c, latticeAdmissible_attained p c, rfl⟩

/-- The normalised relation has no admissible pair at a nonzero layer, so its
sigma-marginal is exactly `{0}`: freezing the lattice is a real restriction and
not a relabelling of the full ladder. -/
theorem normalised_sigma_marginal (k : Int) :
    RightAllowed (fun (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int) =>
      LatticeAdmissible p e k ∧ k = 0) k ↔ k = 0 := by
  constructor
  · rintro ⟨e, -, hk⟩
    exact hk
  · intro hk
    subst hk
    exact ⟨LinearEquiv.refl ℚ_[p] ℚ_[p], latticeAdmissible_refl p, rfl⟩

/-- **Any rectangular repair freezes the lattice layer.** Suppose a sub-relation
`R` of the joint lattice relation is rectangular — that is, suppose a repair
claims independent marginal reasoning is sound for `R`. Then every admissible
pair of `R` sits on one and the same layer: independent marginal reasoning is
available only if the rescaling freedom has already been given up. This is a
statement about the base-field lattice relation, not about any IUT construction. -/
theorem rectangular_subrelation_freezes_layer
    (R : (ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) → Int → Prop)
    (hsub : ∀ (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int), R e k → LatticeAdmissible p e k)
    (hrect : IsRectangular R)
    {e1 e2 : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]} {k1 k2 : Int} (h1 : R e1 k1) (h2 : R e2 k2) :
    k1 = k2 := by
  have hA1 : LatticeAdmissible p e1 k1 := hsub e1 k1 h1
  have hA2 : LatticeAdmissible p e1 k2 := hsub e1 k2 (hrect e1 e2 k1 k2 h1 h2)
  exact latticeAdmissible_unique p e1 hA1 hA2

end

end IUTBridge.Admissibility
