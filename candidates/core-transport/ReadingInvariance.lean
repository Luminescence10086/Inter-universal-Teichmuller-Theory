import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W1 toy province: the reading is invariant under a change of presentation, the partial reading is not

**This file is a toy province for task W1 of the backward plan, and nothing more.** It formalises one
shape and only that shape: *a reading of an object that is determined only up to isomorphism must be
proved independent of the chosen presentation, and a partial reading of the same object is not
invariant.* Concretely, the presentation here is the enumeration of an algorithm's steps
(`Equiv.Perm ℕ`), the reading is the unconditional series sum (`tsum`), and the partial reading is the
finite partial sum (`∑ k ∈ Finset.range n`).

**Why the obligation exists.** `research/core-backward-2026-10-23/h1-decision.md`, §结论一′, quotes
the source (txt lines 8869–8873) defining `n,◦HT^{D-Θ±ellNF}` as the Hodge theater "determined, **up to
isomorphism**, by the various `n,m`-theaters". An object determined only up to isomorphism has no
canonical presentation, so a reading built on it must be proved invariant under a change of
presentation; otherwise the reading lives on a chosen presentation and not on the object. The same
decision records that none of the 11 audited interfaces (`handoffs/core-backward-2026-10-23/M3/`)
carries such an invariance (F3 is false for all of them), so W1 cannot inherit the invariance from the
interfaces and has to prove it.

**This is an analogue of Ind1–Ind3, not Ind1–Ind3.** The permutation group `Equiv.Perm ℕ` stands in
for the change of presentation and `tsum` stands in for the reading; Ind1–Ind3 themselves concern
indeterminacies of the Θ-link. Nothing below constructs a Θ-link, an `Ism`, a prime-strip, a
Frobenioid, a Hodge theater, coricity, or a Galois action, and no claim is made about any of them.

**The substance of the file is item 4, the anti-degeneracy statement.** Invariance of an unconditional
sum under a bijective reindexing is a general topological fact, quoted here from Mathlib
(`Equiv.hasSum_iff`) on top of the existing convergence theorem
`CoreLog.principal_unit_log_hasSum`; convergence is not re-proved. What is *not* general, and is proved
below with a concrete witness, is that the finite partial reading of the same algorithm is **not**
invariant — so "the reading" cannot be taken to be a partial sum. The witness is explicit: at
`x = 4 : ℚ_[3]` the third term of the series is `9` and the first is `3`; reordering the enumeration so
that step 2 is executed first, and stopping after one step, gives `9` against `3` for the identity
enumeration. The two are separated by their norms, `‖9‖ = 1/9 ≠ 1/3 = ‖3‖`, so the failure does not
depend on any totalised value of a divergent series.

**What this file does not establish.** It does not formalise Ind1–Ind3, the Θ-link, `(n,◦)`, or any
other H1 object; it does not show that the invariance obligation of §结论一′ is discharged for the real
object, only that its *shape* — invariant reading, non-invariant partial reading — is consistent and
provable on one concrete complete field. It is not evidence for or against any IUT claim.

Series conventions: the term is the one already used by `CoreTransport.localLog` and by
`PadicLogVolume.logTerm`. `CoreTransport.localLog` and `PadicLogVolume.padicLog` are the same series
written twice (`localLog_eq_padicLog`, by unfolding both definitions), exactly as in
`ExecutionProvenance.lean`; that identification is repeated here only so that this file depends on
`CoreTransport.Basic` and `CoreLog.QpThree` alone.
-/

namespace ReadingInvariance

noncomputable section

open Filter Topology

/-! ## The two presentations, and the reading -/

/-- `CoreTransport.localLog` and `PadicLogVolume.padicLog` are the same series, written twice; this
records that in the open by unfolding both definitions. It carries no mathematical content of its own,
and no later claim rests on the two being secretly different objects. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **The existing convergence result, quoted rather than re-proved.** For `‖x - 1‖ < 1` the logarithm
series sums to `CoreTransport.localLog x`; the proof goes through
`CoreLog.principal_unit_log_summable`, i.e. through the genuine p-adic convergence argument and not
through `tsum`'s totalised default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact CoreLog.principal_unit_log_hasSum hx

/-- **The algorithm run in the order given by `σ`.** The permutation `σ` *is* the presentation: it says
in which order the steps of the algorithm are executed. With `σ = 1` this is the step order
`0, 1, 2, …`. This is the toy stand-in for "the presentation is fixed only up to isomorphism"; see the
module docstring for the exact sense in which it is an analogue only. -/
def partialSumAlong (σ : Equiv.Perm ℕ) (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x (σ k)

/-- The one-step partial sum is exactly the term the presentation picks first. -/
theorem partialSumAlong_one (σ : Equiv.Perm ℕ) (x : ℚ_[3]) :
    partialSumAlong σ x 1 = PadicLogVolume.logTerm x (σ 0) := by
  rw [partialSumAlong, Finset.sum_range_one]

/-- **The reading is the same for every enumeration.** For `‖x - 1‖ < 1`, the sum of the algorithm's
terms taken in the order given by any permutation `σ` still has sum `CoreTransport.localLog x`.

The only input beyond the quoted convergence theorem is that an unconditionally convergent sum is
invariant under a bijective reindexing of its terms; here that is `Equiv.hasSum_iff`
(`HasSum (f ∘ e) a ↔ HasSum f a`, the additive form of `Equiv.hasProd_iff` in
`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`). Convergence is not re-proved. -/
theorem hasSum_perm (σ : Equiv.Perm ℕ) {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (fun n => PadicLogVolume.logTerm x (σ n)) (CoreTransport.localLog x) := by
  have h := (Equiv.hasSum_iff (f := fun k => PadicLogVolume.logTerm x k) σ).mpr
    (hasSum_logTerm_localLog hx)
  simpa only [Function.comp_def] using h

/-- **Two presentations, one reading.** The two sides are kept literally as `tsum`s over the two
enumerations, so the statement is about the presentations and not about `CoreTransport.localLog` by
construction. -/
theorem reading_independent_of_enumeration (σ τ : Equiv.Perm ℕ) {x : ℚ_[3]}
    (hx : ‖x - 1‖ < 1) :
    (∑' n, PadicLogVolume.logTerm x (σ n)) = (∑' n, PadicLogVolume.logTerm x (τ n)) := by
  rw [(hasSum_perm σ hx).tsum_eq, (hasSum_perm τ hx).tsum_eq]

/-! ## Anti-degeneracy: the partial reading is not invariant -/

/-- The first term of the series at `x = 4 : ℚ_[3]` is `3`. -/
theorem logTerm_four_zero : PadicLogVolume.logTerm (4 : ℚ_[3]) 0 = 3 := by
  rw [PadicLogVolume.logTerm_zero]
  norm_num

/-- The third term of the series at `x = 4 : ℚ_[3]` is `9`: `(-1)^2 (4-1)^3 / 3 = 27/3 = 9`. -/
theorem logTerm_four_two : PadicLogVolume.logTerm (4 : ℚ_[3]) 2 = 9 := by
  unfold PadicLogVolume.logTerm
  norm_num

/-- `‖9‖ = 1/9` in `ℚ_[3]`, from `‖3‖ = 1/3` and `9 = 3 ^ 2`. This is the invariant used to separate
the two partial sums of `partialSum_not_invariant`. -/
theorem norm_nine : ‖(9 : ℚ_[3])‖ = (9 : ℝ)⁻¹ := by
  have h : (9 : ℚ_[3]) = 3 ^ 2 := by norm_num
  rw [h, norm_pow, CoreLog.norm_three]
  norm_num

/-- **The partial reading is not invariant.** A concrete failure, not a negated universal: take `σ`
to be the transposition `0 ↔ 2` and stop after `n = 1` step. The transposition executes step `2` at
position `0` of the trace, so the one-step partial sum is the third term `9`; the identity presentation
stopped after one step gives the first term `3`. The two are separated by their norms,
`‖9‖ = 1/9 ≠ 1/3 = ‖3‖`.

This is the point of the file: it is what forbids taking "the reading" to be a partial sum. Note that
the failure is produced by a reordering *within* the same algorithm at the same input `x = 4`, so the
two values differ in a way that the enumeration alone decides. -/
theorem partialSum_not_invariant :
    ∃ (σ : Equiv.Perm ℕ) (n : ℕ),
      partialSumAlong σ (4 : ℚ_[3]) n ≠
        partialSumAlong (1 : Equiv.Perm ℕ) (4 : ℚ_[3]) n := by
  refine ⟨Equiv.swap 0 2, 1, ?_⟩
  have hσ : partialSumAlong (Equiv.swap 0 2) (4 : ℚ_[3]) 1 = (9 : ℚ_[3]) := by
    rw [partialSumAlong_one, Equiv.swap_apply_left, logTerm_four_two]
  have hid : partialSumAlong (1 : Equiv.Perm ℕ) (4 : ℚ_[3]) 1 = (3 : ℚ_[3]) := by
    rw [partialSumAlong_one]
    simpa using logTerm_four_zero
  rw [hσ, hid]
  intro h
  have hnorm : (9 : ℝ)⁻¹ = (3 : ℝ)⁻¹ := by
    rw [← norm_nine, ← CoreLog.norm_three, h]
  norm_num at hnorm

end

end ReadingInvariance

#print axioms ReadingInvariance.localLog_eq_padicLog
#print axioms ReadingInvariance.hasSum_logTerm_localLog
#print axioms ReadingInvariance.partialSumAlong
#print axioms ReadingInvariance.partialSumAlong_one
#print axioms ReadingInvariance.hasSum_perm
#print axioms ReadingInvariance.reading_independent_of_enumeration
#print axioms ReadingInvariance.logTerm_four_zero
#print axioms ReadingInvariance.logTerm_four_two
#print axioms ReadingInvariance.norm_nine
#print axioms ReadingInvariance.partialSum_not_invariant
