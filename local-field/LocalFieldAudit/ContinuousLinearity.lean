import LocalFieldAudit.Filtration
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous additive maps on actual p-adic modules are linear

Additivity gives rational scalar compatibility. Density of the rational numbers
in Mathlib's actual `Q_p`, continuity, and a Hausdorff target extend this to all
p-adic scalars. Thus linearity is proved, not a field of an assumed interface.

The final consequences use actual base-field ideal images from `Filtration`.
Set preservation is still an explicit equality assumption. No Ism element,
Galois module, finite invariant module, logarithm coordinate, log-image identity,
or seed is constructed here. These results do not close RI-01 or any IUT gap.
-/

set_option autoImplicit false

open scoped Pointwise

namespace LocalFieldAudit.ContinuousLinearity

universe u v

variable (p : Nat) [Fact p.Prime]
variable {E : Type u} [AddCommGroup E] [Module ℚ_[p] E]
  [TopologicalSpace E] [ContinuousSMul ℚ_[p] E]
variable {F : Type v} [AddCommGroup F] [Module ℚ_[p] F]
  [TopologicalSpace F] [ContinuousSMul ℚ_[p] F] [T2Space F]

/-- Continuity upgrades automatic rational scalar compatibility to Q_p scalar
compatibility. Neither finite dimension nor completeness is required. -/
theorem map_padic_smul (f : E →+ F) (hf : Continuous f) (a : ℚ_[p]) (x : E) :
    f (a • x) = a • f x := by
  have heq : (fun c : ℚ_[p] => f (c • x)) = fun c : ℚ_[p] => c • f x :=
    (Padic.denseRange_ratCast p).equalizer
      (hf.comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
      (funext fun r => map_ratCast_smul f ℚ_[p] ℚ_[p] r x)
  exact congr_fun heq a

/-- Bundle the proved p-adic linearity with the given continuity. The underlying
function is definitionally the original additive homomorphism. -/
def toPadicContinuousLinearMap (f : E →+ F) (hf : Continuous f) : E →L[ℚ_[p]] F :=
  ⟨{ toFun := f
     map_add' := f.map_add
     map_smul' := map_padic_smul p f hf }, hf⟩

/-- Only forward continuity is needed to upgrade an additive equivalence to an
algebraic Q_p linear equivalence. Inverse continuity is not claimed or assumed. -/
def toPadicLinearEquiv (e : E ≃+ F) (he : Continuous e) : E ≃ₗ[ℚ_[p]] F :=
  { e with map_smul' := map_padic_smul p e.toAddMonoidHom he }

/-- A continuous additive automorphism preserving a set preserves every scalar
layer, with no separate linearity hypothesis and including the zero scalar. -/
theorem image_scalar_layer [T2Space E] (e : E ≃+ E) (he : Continuous e)
    (L : Set E) (hL : e '' L = L) (a : ℚ_[p]) :
    e '' (a • L) = a • L := by
  exact Shell.image_scalar_layer (toPadicLinearEquiv p e he) L hL a

/-- Preservation of the actual base-field maximal-ideal image by a continuous
additive equivalence implies preservation of all integral ideal-power images. -/
theorem preserves_integerIdealImages (e : ℚ_[p] ≃+ ℚ_[p]) (he : Continuous e)
    (hm : e '' Filtration.integerIdealImage p 1 = Filtration.integerIdealImage p 1)
    (n : Nat) :
    e '' Filtration.integerIdealImage p n = Filtration.integerIdealImage p n := by
  let eL := toPadicLinearEquiv p e he
  exact Filtration.preserves_integerIdealImages p eL
    ((Filtration.preserves_maximalIdealImage_iff_ball p eL).mp hm) n

/-- Under the same actual maximal-ideal preservation condition, nonzero elements
have exactly preserved valuation. This is a base-field Q_p conclusion only. -/
theorem preserves_maximalIdealImage_valuation (e : ℚ_[p] ≃+ ℚ_[p]) (he : Continuous e)
    (hm : e '' Filtration.integerIdealImage p 1 = Filtration.integerIdealImage p 1)
    (x : ℚ_[p]) (hx : x ≠ 0) : (e x).valuation = x.valuation := by
  let eL := toPadicLinearEquiv p e he
  exact Filtration.preserves_ball_valuation p eL
    ((Filtration.preserves_maximalIdealImage_iff_ball p eL).mp hm) x hx

/-- The corresponding actual norm conclusion includes zero and requires only
continuity, additivity, bijectivity, and maximal-ideal image preservation. -/
theorem preserves_maximalIdealImage_norm (e : ℚ_[p] ≃+ ℚ_[p]) (he : Continuous e)
    (hm : e '' Filtration.integerIdealImage p 1 = Filtration.integerIdealImage p 1)
    (x : ℚ_[p]) : ‖e x‖ = ‖x‖ := by
  exact Filtration.preserves_maximalIdealImage_norm p (toPadicLinearEquiv p e he) hm x

end LocalFieldAudit.ContinuousLinearity
