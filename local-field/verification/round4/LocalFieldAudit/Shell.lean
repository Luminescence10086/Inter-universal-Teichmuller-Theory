import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Linear preservation of scalar layers of an arbitrary lattice set

`L` is a set, not a subspace over the ambient field. In particular, using this
interface for a `Z_p` lattice does not incorrectly make it a `Q_p` subspace.
The only structural input is that the supplied linear equivalence preserves
`L` as a set. Its preservation of every scalar dilate is then proved.

Threshold transport additionally requires an explicit correspondence between
nonzero-vector layer membership and the proposed measurement. The correspondence
is a hypothesis, not an asserted valuation formula. A logarithm-image identity
for a particular p-adic lattice, and any connection with an IUT packet, remain
unestablished; neither is silently supplied by these generic results.
-/

set_option autoImplicit false

open scoped Pointwise

namespace LocalFieldAudit.Shell

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A genuine linear equivalence preserving an arbitrary set preserves every
scalar dilate of that set, including the zero scalar case. -/
theorem image_scalar_layer (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : K) : e '' (a • L) = a • L := by
  calc
    e '' (a • L) = a • e '' L := Set.image_smul_comm e a L (fun x => e.map_smul a x)
    _ = a • L := by rw [hL]

/-- Injectivity upgrades the layer-image equality to membership equivalence. -/
theorem scalar_layer_membership_iff (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : K) (x : V) : e x ∈ a • L ↔ x ∈ a • L := by
  have himage := image_scalar_layer e L hL a
  constructor
  · intro hx
    have him : e x ∈ e '' (a • L) := by rwa [himage]
    obtain ⟨y, hy, hey⟩ := him
    exact e.injective hey ▸ hy
  · intro hx
    rw [← himage]
    exact ⟨x, hx, rfl⟩

/-- An explicitly supplied nonzero-vector measurement/layer correspondence
converts linear layer preservation into preservation of all displayed strict
thresholds. No valuation or logarithm identity is inferred from linearity. -/
theorem threshold_iff_of_layers (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : Int → K) (cutoff : Int → Int) (measure : V → Int)
    (hmeasure : ∀ (n : Int) (y : V), y ≠ 0 →
      (y ∈ a n • L ↔ cutoff n < measure y))
    (x : V) (hx : x ≠ 0) (n : Int) :
    cutoff n < measure (e x) ↔ cutoff n < measure x := by
  have hex : e x ≠ 0 := by
    intro hzero
    apply hx
    apply e.injective
    simpa using hzero
  exact (hmeasure n (e x) hex).symm.trans
    ((scalar_layer_membership_iff e L hL (a n) x).trans (hmeasure n x hx))

/-- An actual Mathlib `Q_p` module instance with scalar layers `p^n L`.
The primality assumption supplies the p-adic field structure. The measurement
correspondence remains explicit, and no `Z_p` lattice is treated as a `Q_p`
subspace. This theorem establishes no packet or p-adic logarithm realization. -/
theorem padic_threshold_iff (p : Nat) [Fact p.Prime]
    {W : Type v} [AddCommGroup W] [Module ℚ_[p] W]
    (e : W ≃ₗ[ℚ_[p]] W) (L : Set W) (hL : e '' L = L)
    (cutoff : Int → Int) (measure : W → Int)
    (hmeasure : ∀ (n : Int) (y : W), y ≠ 0 →
      (y ∈ ((p : ℚ_[p]) ^ n) • L ↔ cutoff n < measure y))
    (x : W) (hx : x ≠ 0) (n : Int) :
    cutoff n < measure (e x) ↔ cutoff n < measure x := by
  exact threshold_iff_of_layers e L hL (fun m => (p : ℚ_[p]) ^ m)
    cutoff measure hmeasure x hx n

/-- For the actual Mathlib p-adic norm unit ball, preserving the ball implies
preserving all of its `p^n`-layers. This conclusion needs no measurement/layer
correspondence, no logarithm identity, and no nonzero-vector restriction.
The ball is a set of p-adic numbers, not a `Q_p` vector subspace. -/
theorem padic_unitBall_layer_membership_iff (p : Nat) [Fact p.Prime]
    (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hball : e '' {y : ℚ_[p] | ‖y‖ ≤ 1} = {y : ℚ_[p] | ‖y‖ ≤ 1})
    (n : Int) (x : ℚ_[p]) :
    e x ∈ ((p : ℚ_[p]) ^ n) • {y : ℚ_[p] | ‖y‖ ≤ 1} ↔
      x ∈ ((p : ℚ_[p]) ^ n) • {y : ℚ_[p] | ‖y‖ ≤ 1} := by
  exact scalar_layer_membership_iff e {y : ℚ_[p] | ‖y‖ ≤ 1} hball
    ((p : ℚ_[p]) ^ n) x

end LocalFieldAudit.Shell
