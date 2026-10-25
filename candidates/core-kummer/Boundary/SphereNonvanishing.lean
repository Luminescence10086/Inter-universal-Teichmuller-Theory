import Boundary.SphereCoefficientDescent

/-!
# Nonvanishing on the norm-one sphere, reduced to sphere coefficient uniqueness

This module records the contrapositive of
`CoreSphereCoefficientDescent.coeff_eq_of_sphere_values`:

* if a Laurent series `∑' n, b n * u ^ n` is **not** identically zero, then its
  coefficient family `b` is not the zero family (`b_ne_zero_of_value`, which
  uses no completeness and no ultrametric hypothesis);
* if `b` is nonzero and summable at **one** nonzero radius `r`, then some
  norm-one unit `v` has `∑' n, b n * (r * v) ^ n` nonzero
  (`exists_nonzero_on_sphere`).

The second statement is *proved*, not assumed: if every norm-one `v` gave value
`0`, then on the sphere `r * Kˣ` the series of `b` would agree with the series
of the zero family `fun _ => 0`; the sphere comparison theorem then forces
`b = 0`, contradicting the hypothesis. No summability at any other radius, no
annulus covering, and no global Laurent coefficient uniqueness is used.

Status: the two declarations below are compiled in this branch with
`-DwarningAsError=true`; their printed axioms stay inside the standard whitelist.
This is a CLI result, not an editor or fact-tree admission.

## Main results

* `CoreSphereNonvanishing.b_ne_zero_of_value` : a nonzero Laurent value at
  a unit forces the coefficient family to be nonzero.
* `CoreSphereNonvanishing.exists_nonzero_on_sphere` : a nonzero summable family
  is nonzero somewhere on the norm-one sphere around a nonzero radius.
-/

set_option autoImplicit false
noncomputable section

namespace CoreSphereNonvanishing

open TateCurvesTheta TateCurvesTheta.TateParameter

/-- A Laurent series that is not identically zero has a nonzero coefficient
family. No completeness, ultrametric or summability hypothesis is needed: this
is the contrapositive of evaluation being linear in the coefficients.

The summability hypothesis on the zero family is immediately discharged, since
`fun n : ℤ => (0 : K) * (u : K) ^ n` is identically zero. -/
theorem b_ne_zero_of_value
    {K : Type*} [NormedField K] (b : ℤ → K) (u : Kˣ)
    (hvalue : (∑' n : ℤ, b n * (u : K) ^ n) ≠ 0) :
    b ≠ 0 := by
  intro hb
  apply hvalue
  have hzero : ∀ n : ℤ, b n * (u : K) ^ n = (0 : K) := by
    intro n
    simp only [Pi.zero_apply, hb, zero_mul]
  simpa only [tsum_zero] using tsum_congr hzero

/-- **Nonvanishing on one sphere.** Let `b : ℤ → K` be a nonzero coefficient
family that is summable at a single nonzero radius `r`. Then the Laurent
series `∑' n, b n * (r * v) ^ n` is nonzero for some norm-one unit `v`.

Suppose it vanished for every norm-one `v`. Then on that sphere the series of
`b` and the series of the zero family `fun _ => 0` have equal values; the
already proved sphere comparison `coeff_eq_of_sphere_values` (Strassmann
finiteness of zeros on a sphere, at the infinitely many norm-one witnesses
`1 + qᵏ⁺¹`) forces `b` to be the zero family, contradicting `hb`. -/
theorem exists_nonzero_on_sphere
    {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (t : TateParameter K) (b : ℤ → K) (r : Kˣ)
    (hr : Summable (fun n : ℤ => b n * (r : K) ^ n))
    (hb : b ≠ 0) :
    ∃ v : Kˣ, ‖(v : K)‖ = 1 ∧
      (∑' n : ℤ, b n * ((r * v : Kˣ) : K) ^ n) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : Summable (fun n : ℤ => (0 : K) * (r : K) ^ n) := by
    simpa only [zero_mul] using (summable_zero : Summable fun _ : ℤ => (0 : K))
  have heq : ∀ v : Kˣ, ‖(v : K)‖ = 1 →
      (∑' n : ℤ, b n * ((r * v : Kˣ) : K) ^ n) =
        ∑' n : ℤ, (0 : K) * ((r * v : Kˣ) : K) ^ n := by
    intro v hv
    simp only [zero_mul, tsum_zero]
    exact hnone v hv
  have hb0 : b = 0 :=
    CoreSphereCoefficientDescent.coeff_eq_of_sphere_values t b (fun _ : ℤ => (0 : K))
      r hr hzero heq
  exact hb hb0

end CoreSphereNonvanishing

#print axioms CoreSphereNonvanishing.b_ne_zero_of_value
#print axioms CoreSphereNonvanishing.exists_nonzero_on_sphere
