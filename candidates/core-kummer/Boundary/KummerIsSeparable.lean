import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AdjoinRoot
import Boundary.KummerFiniteEtale2

/-! # The Kummer algebra `K[t]/(t² − q)` is a separable field extension

Building on `KummerFiniteEtale2` (`X² − q` irreducible, finite, separable), this
module upgrades polynomial separability to *extension* separability:

```text
Algebra.IsSeparable K (AdjoinRoot (X² − q))
```

The route: `AdjoinRoot.minpoly_root` identifies `minpoly K ρ` with `X² − q`, so
`kummerPoly_separable` gives `IsSeparable K ρ`; then
`IntermediateField.isSeparable_adjoin_simple_iff_isSeparable` transfers this to the
simple extension, and the `AlgEquiv` between the simple extension and the
`AdjoinRoot` carries it across.

Scope: algebra only. No scheme, no tempered cover, no IUT comparison. -/

set_option autoImplicit false
noncomputable section

namespace CoreFiniteEtale

open TateCurvesTheta Polynomial

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- `minpoly K ρ = X² − q` for the adjoined root, since `X² − q` is monic. -/
theorem minpoly_kummerRoot (hq : ¬ IsSquare (t.q : K)) :
    minpoly K (AdjoinRoot.root (kummerPoly t)) = kummerPoly t := by
  have hne : kummerPoly t ≠ 0 := (kummerPoly_irreducible t hq).ne_zero
  rw [AdjoinRoot.minpoly_root hne]
  have hmonic : (kummerPoly t).Monic := by
    simp only [kummerPoly]
    exact monic_X_pow_sub_C _ (by norm_num)
  rw [hmonic.leadingCoeff, inv_one, map_one, mul_one]

/-- **The adjoined Kummer root is separable over `K`.** -/
theorem isSeparable_kummerRoot (hq : ¬ IsSquare (t.q : K)) [_root_.NeZero (2 : K)] :
    _root_.IsSeparable K (AdjoinRoot.root (kummerPoly t)) := by
  rw [_root_.IsSeparable, minpoly_kummerRoot t hq]
  exact kummerPoly_separable t hq


end CoreFiniteEtale

#print axioms CoreFiniteEtale.minpoly_kummerRoot
#print axioms CoreFiniteEtale.isSeparable_kummerRoot
