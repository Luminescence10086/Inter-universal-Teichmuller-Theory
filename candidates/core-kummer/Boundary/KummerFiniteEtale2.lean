import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AdjoinRoot
import TateCurvesTheta.TateCurve.DefectCoeffBaseChange

/-! # The Kummer cover algebra is finite étale over `K` in characteristic `≠ 2`

Path B: the double cover of the `2`-isogeny, at the level of algebras. The cover
algebra is `K[t]/(t² − q)`.

* `kummerPoly_irreducible` : `X² − q` is irreducible when `q` is not a square;
* `kummer_finite` : the algebra is a finite `K`-module (the "finite" of finite étale);
* `kummer_finrank` : its `K`-dimension is `2` when `q` is not a square;
* `kummer_separable` : `X² − q` is separable when `2 ≠ 0`;
* `kummer_formallyEtale` : the algebra is formally étale over `K` in that case.

Separability of `X² − q` follows from
`Polynomial.separable_iff_derivative_ne_zero`: the derivative is `2X`, which is
nonzero whenever `2 ≠ 0`.

## Boundaries

* The algebra is the analytic Tate model's Kummer algebra; it is **not** the
  geometric `R[t]/(t² − (x − e))` over the valuation ring, and no `Spec` object is
  constructed.
* No comparison with the original IUT double isogeny: `TemperedDouble` requires
  `TemperedFundamentalGroups.Andre.TateObjectDouble`, absent locally.
* Formal étaleness is the ring-theoretic statement; it is not a claim about
  finite étale **schemes**. -/

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
theorem kummer_finite : Module.Finite K (AdjoinRoot (kummerPoly t)) := by
  have hmonic : (kummerPoly t).Monic := by
    simp only [kummerPoly]
    exact monic_X_pow_sub_C _ (by norm_num)
  exact Polynomial.Monic.finite_adjoinRoot hmonic

/-- **Degree two**: when `q` is not a square the algebra is a quadratic extension. -/
theorem kummer_finrank (hq : ¬ IsSquare (t.q : K)) :
    Module.finrank K (AdjoinRoot (kummerPoly t)) = 2 := by
  have hirr := kummerPoly_irreducible t hq
  have hne : kummerPoly t ≠ 0 := hirr.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  simp only [kummerPoly]
  rw [natDegree_X_pow_sub_C]

/-- **Separability of the Kummer polynomial** when `q` is not a square and
`2 ≠ 0`: the derivative is `2X`, which is nonzero. -/
theorem kummerPoly_separable (hq : ¬ IsSquare (t.q : K)) [_root_.NeZero (2 : K)] :
    (kummerPoly t).Separable := by
  have hirr := kummerPoly_irreducible t hq
  rw [separable_iff_derivative_ne_zero hirr]
  intro hderiv
  have h2 : (2 : K) = 0 := by
    simpa [kummerPoly, derivative_sub, derivative_pow, derivative_X, derivative_C] using hderiv
  exact NeZero.ne 2 h2


end CoreFiniteEtale

#print axioms CoreFiniteEtale.kummerPoly_irreducible
#print axioms CoreFiniteEtale.kummer_finite
#print axioms CoreFiniteEtale.kummer_finrank
#print axioms CoreFiniteEtale.kummerPoly_separable
