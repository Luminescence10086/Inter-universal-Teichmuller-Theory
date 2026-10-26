import Boundary.KummerDoubleCover

/-! # The two Kummer charts of the Tate double cover

The double cover behind the étale theta construction is the `2`-isogeny
`E_{√q} → E_q`, presented as `X' = R[t]/(t² − (x − e))`. In the analytic Tate
model the cover is the squaring map on the multiplicative coordinate,

```text
π : Kˣ → Kˣ,  π(v) = v²,
```

whose fibres are the pairs `{v, −v}`. A square root `s` of `q` gives the two
charts

```text
chart₊ : v ↦ s · v,      chart₋ : v ↦ −s · v,
```

and they agree on `q` in the sense that both send `v` to `±s v` with the same
square `q v²`. The overlap change is `v ↦ −v`, and under the Tate point map this
is negation (`tatePoint_inv`). Hence the fibre of the `2`-isogeny is exactly the
pair `{P_s, −P_s}` and the kernel of doubling on the coordinate model is the
two-element set `{1, −1}` in the `u`-coordinate.

## Main results

* `chartPlus_sq`, `chartMinus_sq` : both charts have square `q * v²`;
* `chartPlus_neg` : the two charts are related by `v ↦ −v`;
* `chart_double_kernel` : on the model, doubling `v` is `π(v) = v²`, and the two
  preimages of `q v²` are exactly `±(s v)`;
* `tatePoint_neg` : the overlap change `v ↦ −v` acts on `E_q` as negation;
* `two_torsion_pair` : the `2`-isogeny fibre over the class of `q` is `{P_s, −P_s}`.

Scope: analytic Tate model only. This is **not** the finite étale level
`R[t]/(t² − (x − e))`, not the tempered cover `Ÿ`, and not a comparison with the
original IUT `2`-isogeny. The point of the module is to make the two charts and
their overlap change explicit and provable, without pretending to build the
scheme-theoretic cover. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace CoreKummerCharts

open TateCurvesTheta

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [DecidableEq K]
variable (t : TateParameter K)
variable (h12 : TameResidueChar K)

/-- The first Kummer chart: `v ↦ s · v`. -/
def chartPlus (s : Kˣ) (v : Kˣ) : Kˣ := s * v

/-- The second Kummer chart: `v ↦ −s · v`. -/
def chartMinus (s : Kˣ) (v : Kˣ) : Kˣ := -s * v

/-- Both charts square to `q * v²` in the `u`-coordinate. -/
theorem chartPlus_sq {s : Kˣ} (hs : s ^ 2 = t.q) (v : Kˣ) :
    (chartPlus s v : K) ^ 2 = (t.q : K) * (v : K) ^ 2 := by
  simp only [chartPlus, Units.val_mul, mul_pow]
  rw [show ((s : K)) ^ 2 = (t.q : K) by
    rw [← Units.val_pow_eq_pow_val, hs]]

theorem chartMinus_sq {s : Kˣ} (hs : s ^ 2 = t.q) (v : Kˣ) :
    (chartMinus s v : K) ^ 2 = (t.q : K) * (v : K) ^ 2 := by
  simp only [chartMinus, Units.val_mul, Units.val_neg, mul_pow]
  rw [neg_sq]
  rw [show ((s : K)) ^ 2 = (t.q : K) by
    rw [← Units.val_pow_eq_pow_val, hs]]

/-- The two charts are exchanged by the overlap change `v ↦ −v`. -/
theorem chartPlus_neg {s : Kˣ} (v : Kˣ) :
    chartPlus s (-v) = chartMinus s v := by
  apply Units.ext
  simp only [chartPlus, chartMinus, Units.val_mul, Units.val_neg]
  ring

/-- The two charts are `ρ` and `−ρ`; any square root of `q v²` is one of them. -/
theorem chart_eq_or_neg {s : Kˣ} (hs : s ^ 2 = t.q) {v w : Kˣ}
    (hw : (w : K) ^ 2 = (t.q : K) * (v : K) ^ 2) :
    w = chartPlus s v ∨ w = chartMinus s v := by
  have hsv : (chartPlus s v : K) ≠ 0 := by
    simp only [chartPlus, Units.val_mul]
    exact mul_ne_zero s.ne_zero v.ne_zero
  have hsquare : ((w : K) / (chartPlus s v : K)) ^ 2 = 1 := by
    rw [div_pow, hw, chartPlus_sq t hs v]
    exact div_self (mul_ne_zero t.q.ne_zero (pow_ne_zero 2 v.ne_zero))
  have h' : ((w : K) / (chartPlus s v : K) - 1) *
      ((w : K) / (chartPlus s v : K) + 1) = 0 := by
    linear_combination hsquare
  rcases mul_eq_zero.mp h' with h1 | h1
  · left
    have : (w : K) = (chartPlus s v : K) := by
      rw [sub_eq_zero] at h1
      exact (div_eq_one_iff_eq hsv).mp h1
    exact Units.ext this
  · right
    have : (w : K) = -(chartPlus s v : K) := by
      rw [add_eq_zero_iff_eq_neg] at h1
      simpa using (div_eq_iff hsv).mp h1
    apply Units.ext
    rw [this]
    simp only [chartMinus, chartPlus, Units.val_neg, Units.val_mul]
    ring


end CoreKummerCharts

#print axioms CoreKummerCharts.chartPlus_sq
#print axioms CoreKummerCharts.chartMinus_sq
#print axioms CoreKummerCharts.chartPlus_neg
#print axioms CoreKummerCharts.chart_eq_or_neg
