import TateCurvesTheta.TateCurve.TatePointOnCurve
import TateCurvesTheta.TateCurve.GroupLaw
import TateCurvesTheta.Theta.Durfee

/-! # Discharge of `DefectLaurentRepr` and a nontrivial `2`-torsion Tate point

`TatePointOnCurve` proves the Weierstrass defect vanishes off the `q`-orbit
(`tateDefect_eq_zero`), hence the formerly conditional seam `DefectLaurentRepr`
holds with the zero coefficient family (`defectLaurentRepr`). This module audits
those axioms and proves, for a square root `s` of `q`, that the Tate point of `s`
is a nontrivial `2`-torsion point, expressed multiplicatively via `tatePointHom`:

* `deck_sq_eq_one` : `tatePointHom s * tatePointHom s = 1`;
* `deck_sq_ne_one` : `tatePointHom s ≠ 1`.

## Scope and honest boundaries

* Analytic Tate model only. The curve is the explicit Weierstrass model
  `y² + xy = x³ + a₄x + a₆` and the point is `tatePoint s = (X s, Y s)`.
* `TameResidueChar K` is `‖2‖ = 1 ∧ 12 ≠ 0`; in particular characteristic `2`
  is **excluded**. The `2`-torsion statement is not asserted there.
* The former seam does not disappear from the interface: `tatePoint` still takes
  its membership argument `hmem` explicitly, and this module supplies it with
  `memArg` (a def, not a hypothesis). What changed is that `memArg` is now
  provable from `tatePoint_mem'` instead of being an assumed seam.
* No tempered covering, no line bundle `L_N`, no `s₁`/`τ_N`, and no original IUT
  double-isogeny comparison is constructed or claimed here. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace CoreKummerDoubleCover

open TateCurvesTheta

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [DecidableEq K]
variable (t : TateParameter K)

/-- The membership argument supplied by `tatePoint_mem'`, for characteristic prime to `12`. -/
theorem memArg (h12 : TameResidueChar K) :
    ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
      t.tateCurve.toAffine.Equation (t.X u) (t.Y u) :=
  fun _ hu => t.tatePoint_mem' h12.2 hu

/-- **The formerly conditional seam `DefectLaurentRepr` is a theorem.** -/
theorem defectLaurentRepr_closed (h12 : TameResidueChar K) : t.DefectLaurentRepr :=
  t.defectLaurentRepr h12.2

/-- **`tatePoint_mem'` is unconditional** (no seam hypothesis). -/
theorem tatePoint_mem_unconditional (h12 : TameResidueChar K) {u : Kˣ}
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u) :=
  t.tatePoint_mem' h12.2 hu

/-- The point map with the membership argument filled by `memArg`. -/
def tatePointWith (h12 : TameResidueChar K) (u : Kˣ) : t.tateCurve.toAffine.Point :=
  t.tatePoint (memArg t h12) h12 u

/-- **A square root of `q` is not in `qᶻ`.** -/
theorem sq_root_notMem_qpowers {s : Kˣ} (hs : s ^ 2 = t.q) : s ∉ t.qpowers := by
  intro hmem_q
  obtain ⟨n, hn⟩ := t.mem_qpowers_iff_val_eq.mp hmem_q
  have hs2 : ((s : K)) ^ 2 = (t.q : K) := by
    rw [← Units.val_pow_eq_pow_val, hs]
  have h2n : (t.q : K) ^ (2 * n) = (t.q : K) := by
    rw [show (2 : ℤ) * n = n + n by ring, zpow_add₀ t.q.ne_zero, ← hn, ← sq, hs2]
  have h2n1 : (t.q : K) ^ (2 * n) = (t.q : K) ^ (1 : ℤ) := by
    rw [h2n, zpow_one]
  have h1 : (t.q : K) ^ (2 * n - 1) = 1 := by
    rw [zpow_sub₀ t.q.ne_zero, h2n1]
    exact div_self (zpow_ne_zero 1 t.q.ne_zero)
  exact t.zpow_ne_one (by omega) h1

/-- **`tatePointHom s` is `2`-torsion** (multiplicative form). -/
theorem deck_sq_eq_one (h12 : TameResidueChar K) {s : Kˣ} (hs : s ^ 2 = t.q) :
    t.tatePointHom (memArg t h12) h12 s * t.tatePointHom (memArg t h12) h12 s = 1 := by
  have hmul : t.tatePointHom (memArg t h12) h12 (s * s) =
      t.tatePointHom (memArg t h12) h12 s * t.tatePointHom (memArg t h12) h12 s :=
    map_mul _ s s
  have hsq : s * s = t.q := by rw [← sq, hs]
  rw [hsq] at hmul
  have hq : t.tatePointHom (memArg t h12) h12 t.q = 1 := by
    rw [← MonoidHom.mem_ker, t.tatePointHom_ker (memArg t h12) h12]
    exact Subgroup.mem_zpowers t.q
  rw [hq] at hmul
  exact hmul.symm

/-- **`tatePointHom s` is nontrivial.** -/
theorem deck_sq_ne_one (h12 : TameResidueChar K) {s : Kˣ} (hs : s ^ 2 = t.q) :
    t.tatePointHom (memArg t h12) h12 s ≠ 1 := by
  intro h
  have hker : s ∈ t.qpowers := by
    have h0 : s ∈ (t.tatePointHom (memArg t h12) h12).ker := h
    rwa [t.tatePointHom_ker (memArg t h12) h12] at h0
  exact sq_root_notMem_qpowers t hs hker

end CoreKummerDoubleCover

#print axioms CoreKummerDoubleCover.defectLaurentRepr_closed
#print axioms CoreKummerDoubleCover.tatePoint_mem_unconditional
#print axioms CoreKummerDoubleCover.sq_root_notMem_qpowers
#print axioms CoreKummerDoubleCover.deck_sq_eq_one
#print axioms CoreKummerDoubleCover.deck_sq_ne_one
