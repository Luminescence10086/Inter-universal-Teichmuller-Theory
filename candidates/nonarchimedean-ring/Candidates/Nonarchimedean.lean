import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# `NonarchimedeanRing ℚ_[p]`

The research ledger (`research/exploration/RESULTS.md:65`) records that
`NonarchimedeanRing ℚ_[p]` **fails to synthesize** and that this blocks
`HasSum.mul_of_nonarchimedean`. This file builds the missing instance and measures exactly
what it buys.

## The class

`NonarchimedeanRing R` is `Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean:49`:

    class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] : Prop
      extends IsTopologicalRing R where
      is_nonarchimedean : ∀ U ∈ 𝓝 (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U

It is a `Prop`-valued class, so a "bogus" inhabitant is impossible: what has to be supplied is
*genuine mathematics* — for every neighbourhood of `0` an open additive subgroup inside it.

## The proof obligation, made concrete

`ℚ_[p]` is a nonarchimedean normed field (`Padic.nonarchimedean`,
`Mathlib/NumberTheory/Padics/PadicNumbers.lean:834`). Hence a ball `Metric.ball 0 r` is
**closed under addition**: `‖x + y‖ ≤ max ‖x‖ ‖y‖ < r`. Balls are open, contain `0`, and are
closed under negation, so each ball is an `OpenAddSubgroup`. Finally
`Metric.mem_nhds_iff` turns an arbitrary neighbourhood of `0` into such a ball.

## What is *not* claimed

Nothing here is about IUT, Θ-links, log-shells, or any arithmetic deformation theory. This
closes one Lean typeclass obligation of the audit and nothing else. See `README.md` for the
honest accounting of what it does and does not unblock.
-/

open scoped Topology
open Filter

namespace Candidates.Nonarchimedean

variable {p : ℕ} [hp : Fact p.Prime]

/-- A ball around `0` in `ℚ_[p]` is closed under addition. This is where the nonarchimedean
inequality is consumed by the instance below. -/
private lemma add_mem_ball {r : ℝ} {x y : ℚ_[p]}
    (hx : x ∈ Metric.ball (0 : ℚ_[p]) r) (hy : y ∈ Metric.ball (0 : ℚ_[p]) r) :
    x + y ∈ Metric.ball (0 : ℚ_[p]) r := by
  rw [Metric.mem_ball, dist_zero_right] at hx hy ⊢
  exact (Padic.nonarchimedean x y).trans_lt (max_lt hx hy)

/-- **The instance.** Every neighbourhood of `0` in `ℚ_[p]` contains an open additive subgroup:
take a ball `ball 0 ((p:ℝ)⁻¹ ^ n)` inside it. -/
noncomputable instance instNonarchimedeanRingPadic : NonarchimedeanRing ℚ_[p] where
  toIsTopologicalRing := inferInstance
  is_nonarchimedean U hU := by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    have hpinv : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε) (y := (p : ℝ)⁻¹) hε hpinv
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ ^ n := pow_pos (inv_pos.mpr hppos) n
    refine ⟨{ carrier := Metric.ball (0 : ℚ_[p]) ((p : ℝ)⁻¹ ^ n)
              zero_mem' := Metric.mem_ball_self hpos
              add_mem' := fun hx hy => add_mem_ball hx hy
              neg_mem' := by
                intro x hx
                simpa [Metric.mem_ball, dist_zero_right, norm_neg] using hx
              isOpen' := Metric.isOpen_ball }, ?_⟩
    intro x hx
    exact hεU (Metric.ball_subset_ball (le_of_lt hn) hx)

/-! ### Non-vacuity: the instance is inhabited by real content -/

/-- Feeding the instance a specific neighbourhood returns a genuine **subgroup** inside it.
This is the field `is_nonarchimedean` doing actual work, not a placeholder. -/
theorem exists_openAddSubgroup_subset_closedBall :
    ∃ V : OpenAddSubgroup ℚ_[p], (V : Set ℚ_[p]) ⊆ Metric.closedBall (0 : ℚ_[p]) 1 :=
  NonarchimedeanRing.is_nonarchimedean (Metric.closedBall (0 : ℚ_[p]) 1)
    (Metric.closedBall_mem_nhds _ one_pos)

/-- The instance propagates to the additive-group class (this is the class
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` is stated for). -/
theorem nonarchimedeanAddGroup : NonarchimedeanAddGroup ℚ_[p] :=
  NonarchimedeanRing.to_nonarchimedeanAddGroup ℚ_[p]

/-- The nonarchimedean inequality for `ℚ_[p]`.

**Honest labelling:** this does *not* flow through `NonarchimedeanRing`, and no proof of it
could: `NonarchimedeanRing` constrains the *topology*, not the norm. It is
`Padic.nonarchimedean` (`Mathlib/NumberTheory/Padics/PadicNumbers.lean:834`). It is recorded
here because the task asked for it; doing so shows plainly that it is independent of the new
instance. -/
theorem norm_add_le_max (x y : ℚ_[p]) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := Padic.nonarchimedean x y

/-- `ℚ_[p]` is ultrametric.

**Honest labelling:** already available for free as `instIsUltrametricDist p`, i.e. *before* and
*independently of* the instance above. It is not a consequence of `NonarchimedeanRing`. -/
theorem isUltrametricDist : IsUltrametricDist ℚ_[p] := inferInstance

/-! ### Real use test: lemmas whose hypotheses require `NonarchimedeanRing`

`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:113` binds
`[Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]`, so its three exported
theorems are unusable at `R = ℚ_[p]` without the instance. -/

/-- `HasSum.mul_of_nonarchimedean` at `R = ℚ_[p]`
(`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:126`). -/
theorem hasSum_mul (f g : ℕ → ℚ_[p]) (a b : ℚ_[p]) (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun i : ℕ × ℕ => f i.1 * g i.2) (a * b) :=
  HasSum.mul_of_nonarchimedean hf hg

/-- `Summable.mul_of_nonarchimedean` at `R = ℚ_[p]`
(`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:135`). -/
theorem summable_mul (f g : ℕ → ℚ_[p]) (hf : Summable f) (hg : Summable g) :
    Summable (fun i : ℕ × ℕ => f i.1 * g i.2) :=
  hf.mul_of_nonarchimedean hg

/-- `tsum_mul_tsum_of_nonarchimedean` at `R = ℚ_[p]`
(`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:139`): the product formula for
unconditional sums. No existing Mathlib lemma gives this for `ℚ_[p]`. -/
theorem tsum_mul_tsum (f g : ℕ → ℚ_[p]) (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) * (∑' j, g j) = ∑' i : ℕ × ℕ, f i.1 * g i.2 :=
  tsum_mul_tsum_of_nonarchimedean hf hg

/-- `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` at `ℚ_[p]`
(`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:104`, `[to_additive]` of
`multipliable_iff_tendsto_cofinite_one`): unconditional summability in `ℚ_[p]` is equivalent to
the terms tending to zero. This runs through `NonarchimedeanAddGroup ℚ_[p]`, i.e. through the
new instance via `NonarchimedeanRing.to_nonarchimedeanAddGroup`. -/
theorem summable_iff_tendsto_cofinite_zero (f : ℕ → ℚ_[p]) :
    Summable f ↔ Tendsto f cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f

end Candidates.Nonarchimedean
