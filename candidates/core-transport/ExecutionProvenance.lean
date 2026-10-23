import CoreTransport.Basic
import CoreLog.QpThree

/-!
# K4 toy province: execution provenance for the `ℚ_[3]` logarithm

**This file is a toy province for task K4, and nothing more.** The algorithm formalised here is the
partial-sum algorithm of the p-adic logarithm on `ℚ_[3]`: the `n`-th step is the finite sum
`∑_{k<n} (-1)^k (x-1)^{k+1}/(k+1)`. It is **not** the η-algorithm of IUT. Nothing in this file
constructs a Θ-link, an `Ism`, or Corollary 3.12; nothing here touches any object of the external
`iut` interfaces audited in `handoffs/core-backward-2026-10-23/M3/`, and no claim is made about
them.

**The point is type discipline, not new mathematics.** The M3 audit found that in those 11
interfaces an output is a bare structure field (`EtaAlg.out`), while `realisation` only says *where*
outputs land; none of them requires an output to be *produced by a legal execution*. This file is
the smallest honest counter-model of that gap on a concrete complete field:

* `LegalExecution` carries the input, the algorithm's trace **by definitional equality**
  (`steps_eq : steps = algorithmRun input`), the value, and a convergence proof *for that trace*.
  A constant or otherwise chosen sequence cannot be smuggled in, because the trace field is pinned
  to the algorithm rather than merely constrained.
* `value_eq_localLog` derives the value from convergence together with the trace equation, so
  provenance *determines* the value (`value_unique`).
* `value_mem_logImage` is a *consequence* here, not a hypothesis: the value lies in the principal
  unit log image because it is the limit of this algorithm at this input. In the audited interfaces
  the analogous statement (`realisation`) is a field, i.e. a landing condition; that is exactly the
  difference this toy province is built to exhibit.

**What this toy province does not establish.** It says nothing about the IUT η-algorithm, Θ-links,
`Ism`, Corollary 3.12, Galois actions, adelic/hull conditions, localisation, or degree comparisons.
It shows that a provenance-typed interface *can* be written on one concrete example and that such an
interface determines its value; it does **not** show that any IUT interface has been recast in that
form, and it is not evidence for or against any IUT claim.

Series conventions: the term is the one already used by `CoreTransport.localLog` and by
`PadicLogVolume.logTerm`; convergence on principal units is the existing
`CoreLog.principal_unit_log_summable` / `principal_unit_log_hasSum` result, quoted rather than
re-proved.
-/

namespace ExecutionProvenance

noncomputable section

open Filter Topology

/-- **The genuine finite algorithm.** The `n`-th partial sum of the logarithm series at `x`, with
the same term `(-1)^k (x-1)^(k+1)/(k+1)` as `CoreTransport.localLog`.

This is the p-adic logarithm's partial-sum algorithm on `ℚ_[3]`, *not* the η-algorithm of IUT; see
the module docstring. It is a plain definition, so any `LegalExecution` trace is bound to it by
definitional equality (`rfl`), not by a hypothesis. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the existing series term,
definitionally. This is the bridge that lets the trace equation below reach the library's
convergence theorem; it adds no content of its own. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- **Definition-level identification of the two literal series.** `CoreTransport.localLog` and
`PadicLogVolume.padicLog` are the same series, written twice; this records that fact in the open by
unfolding both definitions. It is not mathematical content, and no later claim rests on the two
being secretly different objects.

This is the same statement as `DelegatedLogBridge.localLog_eq_padicLog`. It is repeated here — with
its companion `hasSum_logTerm_localLog` — only because that module is not part of the
`CoreTransport` library target (`lake build DelegatedLogBridge` fails with ``unknown target
`DelegatedLogBridge` ``) and no `DelegatedLogBridge.olean` exists, so importing it would make this
file depend on an artifact Lake does not produce. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **The existing convergence result, quoted.** For `‖x - 1‖ < 1` the series sums to
`CoreTransport.localLog x`; the proof goes through `CoreLog.principal_unit_log_summable`, so it
depends on the genuine p-adic convergence argument and not on `tsum`'s totalised default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact CoreLog.principal_unit_log_hasSum hx

/-- **Execution provenance: a value that exists only together with a named algorithm and a proof
that it is that algorithm's limit.**

The intended reading of each field:

* `input`, `mem` — the input and the domain condition the algorithm needs;
* `steps`, `steps_eq` — the trace *is* `algorithmRun input`, by definitional equality. This field is
  the whole point: without it a trace could be any sequence, e.g. a constant one, and the
  convergence field below would then certify an arbitrary value;
* `value`, `converges` — the limit of that trace.

Because `steps` is pinned to `algorithmRun input`, the pair `(value, converges)` cannot be chosen
freely: `value_eq_localLog` forces `value = CoreTransport.localLog input`. Nothing here refers to
IUT; see the module docstring. -/
structure LegalExecution where
  /-- The input of the execution. -/
  input : ℚ_[3]
  /-- The input lies in the principal-unit domain of the logarithm series. -/
  mem : ‖input - 1‖ < 1
  /-- The trace of the execution, step by step. -/
  steps : ℕ → ℚ_[3]
  /-- The trace **is** the algorithm, by definitional equality: no other sequence is allowed. -/
  steps_eq : steps = algorithmRun input
  /-- The value of the execution. -/
  value : ℚ_[3]
  /-- That value is the limit of that trace. -/
  converges : Filter.Tendsto steps Filter.atTop (𝓝 value)

/-- **Provenance determines the value.** The value of a legal execution is the limit of the
algorithm's partial sums at its input; the limit is unique, so it equals
`CoreTransport.localLog input`. The three ingredients are `converges` (the limit statement),
`steps_eq` (the trace is the algorithm) and `hasSum_logTerm_localLog` (the library's convergence
result); the conclusion is `tendsto_nhds_unique` of the two.

Note which way the dependency runs: the value is *forced* by the trace, and the trace is forced by
the algorithm. The proof cannot be reproduced with a constant trace, because then `steps_eq` would
have to prove a constant sequence equal to `algorithmRun input`. -/
theorem value_eq_localLog (e : LegalExecution) : e.value = CoreTransport.localLog e.input := by
  -- the trace, being the algorithm, converges to the value the structure records
  have hrun : Tendsto (algorithmRun e.input) Filter.atTop (𝓝 e.value) := by
    rw [← e.steps_eq]
    exact e.converges
  have hsteps : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm e.input k)
      Filter.atTop (𝓝 e.value) := by
    simpa only [algorithmRun_eq_partialSums] using hrun
  -- the same partial sums converge to `localLog`, by the existing Q_3 theorem
  have hlog : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm e.input k)
      Filter.atTop (𝓝 (CoreTransport.localLog e.input)) :=
    (hasSum_logTerm_localLog e.mem).tendsto_sum_nat
  exact tendsto_nhds_unique hsteps hlog

/-- **Provenance determines the value**, as a statement about two executions: same input, hence same
value. No further data is consulted — not the chosen trace, not the chosen value, not any region the
value might land in. -/
theorem value_unique {e₁ e₂ : LegalExecution} (h : e₁.input = e₂.input) :
    e₁.value = e₂.value := by
  rw [value_eq_localLog e₁, value_eq_localLog e₂, h]

/-- **Anti-degeneracy, as a consequence rather than a condition.** The value of a legal execution
lies in the principal-unit log image `CoreTransport.logImage ℚ_[3]`.

This is deliberately *not* an assumption of `LegalExecution`: it follows from `value_eq_localLog`,
i.e. from the fact that the value is the algorithm's limit. It is recorded to make the contrast with
the audited interfaces explicit — there, the analogous statement is a structure field
(`EtaAlg.realisation`), i.e. a landing condition, and a landing condition alone can never determine
a value. See `logImage_Q3_eq_closedBall` for how weak that condition is. -/
theorem value_mem_logImage (e : LegalExecution) : e.value ∈ CoreTransport.logImage ℚ_[3] :=
  ⟨e.input, e.mem, (value_eq_localLog e).symm⟩

/-- **Why a landing condition cannot replace provenance.** The principal-unit log image of `ℚ_[3]`
is the whole closed ball of radius `‖3‖ = 1/3`, not a single point: membership in it is satisfied by
an entire ball of values, so it can never pin down which value an execution produced.

This is the same statement as `DelegatedLogBridge.logImage_Q3_eq_closedBall`, obtained here from
`CoreLog.principal_unit_log_image` through the definition-level identification of the two literal
series (`localLog_eq_padicLog`). -/
theorem logImage_Q3_eq_closedBall :
    CoreTransport.logImage ℚ_[3] = {y : ℚ_[3] | ‖y‖ ≤ (3 : ℝ)⁻¹} := by
  unfold CoreTransport.logImage
  rw [show (CoreTransport.localLog : ℚ_[3] → ℚ_[3]) = PadicLogVolume.padicLog from
    funext localLog_eq_padicLog]
  exact CoreLog.principal_unit_log_image

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`. -/
theorem norm_four_sub_one : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- **Non-vacuity.** A concrete legal execution at the input `4 : ℚ_[3]`, with the genuine trace
`algorithmRun 4` and the value it forces. Every field is discharged by an actual proof: `mem` by
`norm_four_sub_one`, `steps_eq` by `rfl` (definitional equality with the algorithm), `converges` by
the existing convergence theorem composed with `algorithmRun_eq_partialSums`. -/
def witnessFour : LegalExecution where
  input := 4
  mem := norm_four_sub_one
  steps := algorithmRun 4
  steps_eq := rfl
  value := CoreTransport.localLog 4
  converges := by
    rw [algorithmRun_eq_partialSums]
    exact (hasSum_logTerm_localLog norm_four_sub_one).tendsto_sum_nat

/-- The non-vacuity witness, at the type `LegalExecution` itself: the structure is inhabited by an
actual execution at the input `4`. -/
example : LegalExecution := witnessFour

end

end ExecutionProvenance

#print axioms ExecutionProvenance.algorithmRun
#print axioms ExecutionProvenance.algorithmRun_eq_partialSums
#print axioms ExecutionProvenance.localLog_eq_padicLog
#print axioms ExecutionProvenance.hasSum_logTerm_localLog
#print axioms ExecutionProvenance.value_eq_localLog
#print axioms ExecutionProvenance.value_unique
#print axioms ExecutionProvenance.value_mem_logImage
#print axioms ExecutionProvenance.logImage_Q3_eq_closedBall
#print axioms ExecutionProvenance.norm_four_sub_one
#print axioms ExecutionProvenance.witnessFour
