import LocalFieldAudit.Filtration
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# The valuation ledger of actual p-adic rescaling

This module builds the *arithmetic* side of a bridge between two previously
separate theory bodies of this repository:

* the abstract discrete scaling model `IUTAudit.Scale` in the main project, and
* the audited real `Q_p` filtration of `LocalFieldAudit.Filtration`.

The bridge object is the integer norm-layer ladder `layer p k` of the actual
p-adic unit ball together with the actual rescaling automorphism `shift p n`
(multiplication by `p^n`). The ladder is *antitone* in the index: `layer k` is the
ball of radius `p^(-k)`, so a larger index is a smaller ball. Two ledgers are
computed for the same object:

* the **norm ledger** is multiplicative: the scale factor of a composite is the
  product of the two factors;
* the **valuation ledger** is additive: `(shift n (shift m x)).valuation = n + m + x.valuation`.

Telescoping over a list of exponents is then path independent: the composite
rescaling equals the rescaling by the list sum. This is the exact integer
bookkeeping that the abstract model only assumes, and it is what a discrete
"container widening" costs in the base field.

Scope. Everything here is the **base field** `Q_p` of Mathlib, with finite
valuation on nonzero elements. No ramified extension, no normalization of a
general discretely valued field, no `log_p(O^×)` image identity, no Ism/Kummer
element, no IUT packet and no Arakelov log-volume is constructed. `layer` is a
set of p-adic numbers, never a `Q_p`-subspace. These results therefore do not
close G01/G03 and say nothing about Corollary 3.12 or abc.
-/

set_option autoImplicit false

open scoped Pointwise

namespace IUTBridge.ScaleLedger

noncomputable section

variable (p : Nat) [hp : Fact p.Prime]

/-- p is a nonzero p-adic scalar. -/
theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

/-- p is a nonzero real scalar. -/
theorem pR_ne_zero : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- p is a positive real number. -/
theorem pR_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

/-- `1 < p` as a real number, used for strict monotonicity of integral powers. -/
theorem one_lt_pR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

/-- The integer norm-layer ladder of the actual p-adic unit ball:
`layer k` is `p^k · ball`, the ball of radius `p^(-k)`, a set of p-adic numbers
and not a subspace. The ladder is antitone: larger index, smaller ball. -/
def layer (k : Int) : Set ℚ_[p] := ((p : ℚ_[p]) ^ k) • LocalFieldAudit.Filtration.ball p

/-- Norm reading of a layer, including zero: no valuation is involved. -/
theorem mem_layer_iff_norm_le (k : Int) (x : ℚ_[p]) :
    x ∈ layer p k ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) :=
  LocalFieldAudit.Filtration.mem_zpow_ball_iff_norm_le p k x

/-- Valuation reading of a layer. The finite valuation is only defined on
nonzero elements, so the zero element is excluded here on purpose. Larger index
means a strictly smaller set: `layer k = {x | k ≤ v x}`. -/
theorem mem_layer_iff_le_valuation (k : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    x ∈ layer p k ↔ k ≤ x.valuation :=
  LocalFieldAudit.Filtration.mem_zpow_ball_iff_le_valuation p k x hx

/-- Zero belongs to every layer of the ladder. -/
theorem zero_mem_layer (k : Int) : (0 : ℚ_[p]) ∈ layer p k := by
  rw [mem_layer_iff_norm_le, norm_zero]
  exact (zpow_pos (pR_pos p) (-k)).le

/-- The actual rescaling automorphism `x ↦ p^n · x` of `Q_p`. -/
def shift (n : Int) : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p] :=
  LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] ((p : ℚ_[p]) ^ n) (zpow_ne_zero n (p_ne_zero p))

/-- The underlying function of `shift` is multiplication by `p^n`. -/
theorem shift_apply (n : Int) (x : ℚ_[p]) : shift p n x = (p : ℚ_[p]) ^ n * x := rfl

/-- **Ledger composition.** Iterated rescaling adds exponents. This is the
arithmetic counterpart of composition in the discrete scale model. -/
theorem shift_comp_apply (n m : Int) (x : ℚ_[p]) :
    shift p n (shift p m x) = shift p (n + m) x := by
  rw [shift_apply, shift_apply, shift_apply, ← mul_assoc, ← zpow_add₀ (p_ne_zero p)]

/-- **Norm ledger.** Rescaling multiplies the norm by the exact factor `p^(-n)`. -/
theorem norm_shift (n : Int) (x : ℚ_[p]) :
    ‖shift p n x‖ = (p : ℝ) ^ (-n) * ‖x‖ := by
  rw [shift_apply, norm_mul, Padic.norm_p_zpow]

/-- **Multiplicativity of the norm ledger** over a composite rescaling. -/
theorem norm_factor_composition (n m : Int) (x : ℚ_[p]) :
    ‖shift p n (shift p m x)‖ = (p : ℝ) ^ (-n) * ((p : ℝ) ^ (-m) * ‖x‖) := by
  rw [norm_shift, norm_shift]

/-- The composite scale factor is exactly `p^(-(n+m))`, as the abstract model
predicts for a product of scales. -/
theorem norm_factor_pow (n m : Int) (x : ℚ_[p]) :
    ‖shift p n (shift p m x)‖ = (p : ℝ) ^ (-(n + m)) * ‖x‖ := by
  rw [shift_comp_apply, norm_shift, neg_add, zpow_add₀ (pR_ne_zero p)]

/-- **Valuation ledger.** On nonzero elements the additive valuation moves by
exactly the exponent. -/
theorem valuation_shift (n : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    (shift p n x).valuation = n + x.valuation := by
  rw [shift_apply, Padic.valuation_mul (zpow_ne_zero n (p_ne_zero p)) hx,
    Padic.valuation_zpow, Padic.valuation_p, mul_one]

/-- Rescaling preserves nonzero elements. -/
theorem shift_ne_zero (n : Int) (x : ℚ_[p]) (hx : x ≠ 0) : shift p n x ≠ 0 := by
  rw [shift_apply]
  exact mul_ne_zero (zpow_ne_zero n (p_ne_zero p)) hx

/-- **Additivity of the valuation ledger** over composite rescalings. -/
theorem valuation_ledger_composition (n m : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    (shift p n (shift p m x)).valuation = n + m + x.valuation := by
  rw [valuation_shift p n _ (shift_ne_zero p m x hx), valuation_shift p m x hx]
  omega

/-- **The ladder moves by the exponent.** The image of layer `k` under `shift n`
is layer `k + n`; a rescaling never changes the ladder's own shape. -/
theorem layer_image_shift (n k : Int) : shift p n '' layer p k = layer p (k + n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · subst hx0
      rw [map_zero]
      exact zero_mem_layer p (k + n)
    · have hv : ((p : ℚ_[p]) ^ n * x).valuation = n + x.valuation := by
        rw [Padic.valuation_mul (zpow_ne_zero n (p_ne_zero p)) hx0,
          Padic.valuation_zpow, Padic.valuation_p, mul_one]
      rw [shift_apply, mem_layer_iff_le_valuation _ _ _
        (mul_ne_zero (zpow_ne_zero n (p_ne_zero p)) hx0), hv, add_comm k n]
      exact Int.add_le_add_left ((mem_layer_iff_le_valuation p k x hx0).mp hx) n
  · intro hy
    by_cases hy0 : y = 0
    · subst hy0
      exact ⟨0, zero_mem_layer p k, by rw [map_zero]⟩
    · refine ⟨(p : ℚ_[p]) ^ (-n) * y, ?_, ?_⟩
      · rw [mem_layer_iff_le_valuation _ _ _
          (mul_ne_zero (zpow_ne_zero (-n) (p_ne_zero p)) hy0)]
        have hv : ((p : ℚ_[p]) ^ (-n) * y).valuation = -n + y.valuation := by
          rw [Padic.valuation_mul (zpow_ne_zero (-n) (p_ne_zero p)) hy0,
            Padic.valuation_zpow, Padic.valuation_p, mul_one]
        rw [hv]
        have hle := (mem_layer_iff_le_valuation p (k + n) y hy0).mp hy
        omega
      · rw [shift_apply, ← mul_assoc, ← zpow_add₀ (p_ne_zero p),
          show n + -n = 0 by omega, zpow_zero, one_mul]

/-- **Subset in the contract direction.** A larger index gives a smaller ball. -/
theorem layer_subset_of_le {k m : Int} (h : k ≤ m) : layer p m ⊆ layer p k := by
  intro x hx
  rw [mem_layer_iff_norm_le] at hx ⊢
  exact hx.trans ((zpow_le_zpow_iff_right₀ (one_lt_pR p)).mpr (by omega))

/-- **Strict monotonicity.** Distinct indices give genuinely different balls, so
the ladder is an infinite filtration and not one repeated set. -/
theorem layer_ssubset_of_lt {k m : Int} (h : k < m) : layer p m ⊂ layer p k := by
  refine ⟨layer_subset_of_le p h.le, ?_⟩
  intro hsub
  have hmem : (p : ℚ_[p]) ^ k ∈ layer p k := by
    rw [mem_layer_iff_le_valuation _ _ _ (zpow_ne_zero k (p_ne_zero p)),
      Padic.valuation_zpow, Padic.valuation_p, mul_one]
  have hkm := hsub hmem
  rw [mem_layer_iff_le_valuation _ _ _ (zpow_ne_zero k (p_ne_zero p)),
    Padic.valuation_zpow, Padic.valuation_p, mul_one] at hkm
  omega

/-- The ladder is injective as a function of its index. -/
theorem layer_injective : Function.Injective (layer p) := by
  intro k m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := layer_ssubset_of_lt p hlt
    rw [h] at this
    exact this.2 subset_rfl
  · have := layer_ssubset_of_lt p hlt
    rw [h] at this
    exact this.2 subset_rfl

/-- **Exact container-widening cost.** Moving the ladder container from `layer k`
to `layer m` is realized by the single dilation of exponent `m - k`; in the base
field the cost of widening is therefore exactly that exponent difference and
nothing else. -/
theorem cost_exact (k m : Int) : shift p (m - k) '' layer p k = layer p m := by
  rw [layer_image_shift, show k + (m - k) = m by omega]

/-- A `Q_p`-linear endomorphism of `Q_p` is determined by its value at `1`.
This is the arithmetic counterpart of a scale being determined at the unit. -/
theorem map_one_determines (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (x : ℚ_[p]) :
    e x = e 1 * x := by
  have h : e (x • (1 : ℚ_[p])) = x • e 1 := LinearEquiv.map_smul e x 1
  simpa [smul_eq_mul, mul_comm] using h

/-- An automorphism sends the ball onto the layer indexed by the valuation of its
value at `1`: the image of the unit determines the lattice layer completely. -/
theorem image_ball_eq_layer (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) :
    e '' LocalFieldAudit.Filtration.ball p = layer p (e 1).valuation := by
  have he1 : e 1 ≠ 0 := by
    have h1 : (1 : ℚ_[p]) ≠ 0 := one_ne_zero
    intro h0
    exact h1 (e.injective (by rw [h0, map_zero]))
  have hnorm : ‖e 1‖ = (p : ℝ) ^ (-(e 1).valuation) := Padic.norm_eq_zpow_neg_valuation he1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := hx
    rw [mem_layer_iff_norm_le, map_one_determines, norm_mul, hnorm]
    exact mul_le_of_le_one_right (zpow_pos (pR_pos p) _).le hx'
  · intro hy
    have hyle : ‖y‖ ≤ ‖e 1‖ := by
      rw [hnorm]
      exact (mem_layer_iff_norm_le p _ y).mp hy
    obtain ⟨z, hz, hzy⟩ :=
      (LocalFieldAudit.Filtration.mem_smul_ball_iff_norm_le p (e 1) y he1).mpr hyle
    refine ⟨z, hz, ?_⟩
    calc e z = e 1 * z := map_one_determines p e z
      _ = y := by
        have h : (e 1) • z = y := hzy
        simpa [smul_eq_mul] using h

/-- **Every automorphism determines exactly one lattice layer.** This is the
arithmetic realization of "a scale is determined by its value on the unit": the
joint data (automorphism, layer) is a graph, never a product. -/
theorem existsUnique_layer_of_auto (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) :
    ∃! k : Int, e '' LocalFieldAudit.Filtration.ball p = layer p k := by
  refine ⟨(e 1).valuation, image_ball_eq_layer p e, ?_⟩
  intro k hk
  exact layer_injective p (hk.symm.trans (image_ball_eq_layer p e))

/-- Composite rescaling along a list of integer exponents. -/
def composeShift : List Int → ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]
  | [] => LinearEquiv.refl ℚ_[p] ℚ_[p]
  | n :: ns => (composeShift ns).trans (shift p n)

/-- The composite rescaling acts by multiplication by `p` to the list sum. -/
theorem composeShift_apply (l : List Int) (x : ℚ_[p]) :
    composeShift p l x = (p : ℚ_[p]) ^ l.sum * x := by
  induction l with
  | nil => simp [composeShift]
  | cons n ns ih =>
      simp only [composeShift, LinearEquiv.trans_apply, ih, shift_apply, List.sum_cons]
      have hexp : (p : ℚ_[p]) ^ n * (p : ℚ_[p]) ^ ns.sum =
          (p : ℚ_[p]) ^ (n + ns.sum) := by
        rw [← zpow_add₀ (p_ne_zero p)]
      rw [← mul_assoc, hexp]

/-- **Telescoping / path independence.** The composite of the rescalings along a
list equals the single rescaling by the list sum, so the ledger is an additive
invariant of the chain and not of its presentation. -/
theorem composeShift_eq_shift_sum (l : List Int) : composeShift p l = shift p l.sum := by
  ext x
  rw [composeShift_apply, shift_apply]

end

end IUTBridge.ScaleLedger
