import Boundary.AnnularConvergence

/-! Sphere geometry inside the q-atlas closed annuli.
The unit sphere `{v : Kˣ | ‖v‖ = 1}` is the overlap locus of adjacent q-annuli:
multiplying the central q-power `t.q ^ m` by any point of the sphere stays in the
`m`-th annulus, and also in the `(m+1)`-st annulus. Both statements are pure
multiplicativity of the norm (`‖a * b‖ = ‖a‖ * ‖b‖`) applied to the already
proved containment of `t.q ^ m` in the corresponding annulus; no summability,
completeness, ultrametricity or discreteness hypothesis is used or introduced.
This file records only that metric bookkeeping; the analytic overlap comparison
itself is elsewhere and is not claimed here. -/

set_option autoImplicit false
noncomputable section

namespace CoreAnnularOverlap

open TateCurvesTheta CoreAnnularConvergence

variable {K : Type*} [NormedField K]

/-- A point of the central q-shell times a point of the multiplicative unit
sphere lies in the closed annulus indexed by the same integer `m`. -/
theorem qpow_mul_mem_annulus (t : TateParameter K) (m : ℤ) (v : Kˣ)
    (hv : ‖(v : K)‖ = 1) : InQClosedAnnulus t m (t.q ^ m * v) := by
  have h := qpow_mem_q_closed_annulus t m
  have hnorm : ‖((t.q ^ m * v : Kˣ) : K)‖ = ‖((t.q ^ m : Kˣ) : K)‖ := by
    rw [Units.val_mul, norm_mul, hv, mul_one]
  simp only [InQClosedAnnulus] at h ⊢
  rw [hnorm]
  exact h

/-- The same point lies in the closed annulus indexed by `m + 1`: the central
q-shell of one annulus is the overlap sphere with the next one. -/
theorem qpow_mul_mem_next_annulus (t : TateParameter K) (m : ℤ) (v : Kˣ)
    (hv : ‖(v : K)‖ = 1) : InQClosedAnnulus t (m + 1) (t.q ^ m * v) := by
  have h := qpow_mem_next_q_closed_annulus t m
  have hnorm : ‖((t.q ^ m * v : Kˣ) : K)‖ = ‖((t.q ^ m : Kˣ) : K)‖ := by
    rw [Units.val_mul, norm_mul, hv, mul_one]
  simp only [InQClosedAnnulus] at h ⊢
  rw [hnorm]
  exact h

end CoreAnnularOverlap

#print axioms CoreAnnularOverlap.qpow_mul_mem_annulus
#print axioms CoreAnnularOverlap.qpow_mul_mem_next_annulus
