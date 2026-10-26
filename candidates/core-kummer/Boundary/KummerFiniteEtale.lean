import Mathlib.RingTheory.AdjoinRoot
import TateCurvesTheta.TateCurve.DefectCoeffBaseChange

/-! # The Kummer cover algebra `K[t]/(t² − q)` is finite over `K`

Path B asks for the finite étale double cover built from a real `2`-torsion point.
The algebraic core is the Kummer algebra `K[t]/(t² − q)`. This module proves the
part that does not depend on separability API choices:

* `K[t]/(t² − q)` is a **finite** `K`-module, for every Tate parameter;
* when `q` is not a square, `X² − q` is irreducible, so the algebra is a field
  extension of degree `2`.

Finiteness is what "finite" in "finite étale" requires; étaleness additionally
needs separability of `X² − q`, which holds whenever `2 ≠ 0` in `K`. That
separability step is **not** claimed here.

## Main results

* `kummerPoly_irreducible` : `X² − q` is irreducible when `q` is not a square;
* `kummer_finite` : `Module.Finite K (AdjoinRoot (X² − q))`;
* `kummer_finrank` : the extension has `K`-dimension `2` when `q` is not a square.

Scope: algebra only. No scheme, no tempered cover, no original IUT comparison. -/

set_option autoImplicit false
noncomputable section

namespace CoreFiniteEtale

open TateCurvesTheta Polynomial

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The Kummer polynomial `X² − q`. -/
def kummerPoly : K[X] := X ^ 2 - C (t.q : K)

/-- When `q` is not a square, the Kummer polynomial is irreducible. -/
theorem kummerPoly_irreducible (hq : ¬ IsSquare (t.q : K)) :
    Irreducible (kummerPoly t) := by
  have h : Irreducible (X ^ 2 - C (t.q : K)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => hq ⟨b, by rw [← hb, sq]⟩
  simpa only [kummerPoly] using h

/-- **Finiteness**: the Kummer cover algebra is a finite `K`-module. -/
theorem kummer_finite :
    Module.Finite K (AdjoinRoot (kummerPoly t)) := by
  have hmonic : (kummerPoly t).Monic := by
    simp only [kummerPoly]
    exact monic_X_pow_sub_C _ (by norm_num)
  exact Polynomial.Monic.finite_adjoinRoot hmonic

/-- **Degree `2`**: when `q` is not a square, the Kummer algebra is a quadratic
extension of `K`. -/
theorem kummer_finrank (hq : ¬ IsSquare (t.q : K)) :
    Module.finrank K (AdjoinRoot (kummerPoly t)) = 2 := by
  have hirr := kummerPoly_irreducible t hq
  have hne : kummerPoly t ≠ 0 := hirr.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  simp only [kummerPoly]
  rw [natDegree_X_pow_sub_C]

end CoreFiniteEtale

#print axioms CoreFiniteEtale.kummerPoly_irreducible
#print axioms CoreFiniteEtale.kummer_finite
#print axioms CoreFiniteEtale.kummer_finrank
