import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W2 toy province: execution provenance for a local-global *collection*, not for a single element

**This file is a toy province for task W2 of the backward plan, and nothing more.** K4
(`candidates/core-transport/ExecutionProvenance.lean`) put execution provenance on a *single*
element: an object whose value exists only together with a named algorithm and a proof that the value
is that algorithm's limit. This file lifts that type from one element to a **collection** and proves
that provenance determines the reading of the whole collection, not merely of one piece.

**Why a collection and not an element.** `research/core-backward-2026-10-23/h1-decision.md`, §结论二,
quotes the source (txt lines 8607–8629) defining the category `⊼fQ₂` of "local-global collections" and
its `⊼`-version `⊼fQ₁`, and the "local-global `⊼`-collections" `⊼lc₁` of txt 8566–8571; the objects
there consist of local pieces indexed by the places of a number field, one global object, and
localisation morphisms relating them. This file models that **shape at the set level only**, with
`Fin n` in place of the set of places:

* `localInput v`, `mem v` — the `n` local inputs, each in the principal-unit domain;
* `localSteps v`, `steps_eq v` — each local piece is **produced** by the algorithm, by definitional
  equality with `algorithmRun (localInput v)`, exactly as in K4;
* `localValue v`, `converges v` — each local reading is the limit of that local trace;
* `globalValue`, `localization` — one global reading, related to the local readings.

**The `localization` field is a toy stand-in, and a degenerate one.** In the source it is a family of
localisation *morphisms* between genuinely different objects, with a nontrivial compatibility
structure. Here it is the single equation `globalValue = localValue v` for every `v`: the global
reading is *the common local reading*. That is the crudest possible stand-in for localisation and it
is stated as such — it captures only the one feature this file needs, namely that the global reading is
tied to the local ones rather than being free. It is **not** IUT's localisation, and no claim below is
about IUT's localisation.

**What is proved.**

* `localValue_determined` — componentwise, each local reading is `CoreTransport.localLog` of its own
  input, from `converges`, `steps_eq` and the quoted convergence theorem, by uniqueness of limits.
* `localValues_determined` — the whole local reading *function* is determined, not one component.
* `globalValue_determined_at` / `globalValue_determined` — the global reading is likewise fixed, at an
  arbitrary index and (as required) at the index `0`.
* `both_readings_unique` — two collections with the same local inputs have the same local reading
  function and the same global reading: provenance ties the reading to the input data alone.
* `localValue_mem_logImage`, `landing_of_provenance` — every local reading lies in the principal-unit
  log image `CoreTransport.logImage ℚ_[3]`. This is a **consequence**, not a field: the whole contrast
  of this file is that landing is derived from provenance, never assumed in its place.

**The anti-degeneracy statement, stated precisely.** What is proved is the *preferred* form:
`landing_does_not_determine_global` exhibits **two collections with the same `n`** (namely `n = 1`),
each of whose local readings lies in `CoreTransport.logImage ℚ_[3]` — so both satisfy the landing
predicate in the strongest available sense, as a theorem about them — whose **global readings differ**.
`landing_does_not_determine_global_nontrivial` repeats the separation with two inputs that are both
different from `1`, so the failure is not an artefact of the trivial input.

The fallback offered in the task statement — one collection with `n = 1` against one with `n = 2` —
was **not needed**: the toy's `localization` field does *not* make the same-`n` statement impossible.
The field forces the global reading to equal a local one, and two collections with `n = 1` may still
have different local readings, hence different global readings; nothing in `localization` compares two
*different* collections. What the toy does make impossible is the superficially stronger statement
"same local readings, different global reading": `both_readings_unique` proves that two collections
with the same `localInput` have the same `globalValue`, so a separation can only be produced by data
the landing predicate does not see — the inputs. That is exactly the honest content: the landing
predicate is a property of values alone, and it is satisfied by collections whose readings are
different values, while provenance is a property of the trace and pins the reading.

**Not a circularity, and where the work is.** Nothing above assumes the conclusion: `localValue` and
`globalValue` are arbitrary fields of the structure, and the theorems *derive* their values from
`steps_eq` (definitional equality with the algorithm) plus `converges`. The separation lemmas are
concrete computations on `ℚ_[3]` (`localLog 4 ≠ 0`, `localLog 4 ≠ localLog (-2)`), obtained from the
existing rearrangement `PadicLogVolume.padicLog_one_add` and its remainder estimate
`PadicLogVolume.norm_logRem_le` — no new analysis of the logarithm is performed here.

**What this toy province does not establish.** It says nothing about the IUT η-algorithm, Θ-links,
`Ism`, Corollary 3.12, prime-strips, Frobenioids, Hodge theaters, Galois actions, adelic/hull
conditions, the category `⊼fQ₂`, its `⊼`-version `⊼fQ₁`, or the formal quotient `⊼fQ₂ modulo ⊼fQ₁` of
§结论二. `Fin n` is a set of indices, not a set of places; `localization` is one equation, not a family
of morphisms; and the logarithm series on `ℚ_[3]` is not the η-algorithm. The file shows that a
provenance-typed *collection* can be written and that it determines its own reading while a landing
predicate does not; it is not evidence for or against any IUT claim.

**Why the two quoted lemmas are re-derived here.** `ExecutionProvenance.lean` is not a target of the
Lake library `CoreTransport` (`lakefile.lean` declares only `lean_lib CoreTransport`), so no
`ExecutionProvenance.olean` is produced and `import ExecutionProvenance` is not available; the file was
checked as a standalone module. The same holds for `ReadingInvariance.lean`. Accordingly this file
re-states `algorithmRun` and re-derives `localLog_eq_padicLog` and `hasSum_logTerm_localLog` locally,
exactly as K4 and W1 each did, so that it depends on `CoreTransport.Basic` and `CoreLog.QpThree` alone.
The re-derivation is an identification of two literal series by unfolding both definitions; it adds no
mathematical content, and no claim rests on the two being secretly different objects.

Series conventions: the term is the one already used by `CoreTransport.localLog` and by
`PadicLogVolume.logTerm`; convergence on principal units is the existing
`CoreLog.principal_unit_log_hasSum`, quoted rather than re-proved.
-/

namespace CollectionProvenance

noncomputable section

open Filter Topology

/-! ## The algorithm, and the quoted convergence theorem -/

/-- **The genuine finite algorithm, re-stated.** The `n`-th partial sum of the logarithm series at
`x`, with the same term `(-1)^k (x-1)^(k+1)/(k+1)` as `CoreTransport.localLog`.

This is a re-statement of `ExecutionProvenance.algorithmRun`, not a new algorithm: the latter's module
is not a target of the Lake library, so it has no compiled interface to import (see the module
docstring). As in that file, this is the p-adic logarithm's partial-sum algorithm on `ℚ_[3]`, *not* the
η-algorithm of IUT. Being a plain definition, it binds any trace in `LocalGlobalCollection` by
definitional equality (`rfl`), not by a hypothesis. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the existing series term,
definitionally. This is the bridge from the trace equation to the library's convergence theorem; it
adds no content of its own. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- `CoreTransport.localLog` and `PadicLogVolume.padicLog` are the same series, written twice; this
records that in the open by unfolding both definitions. Re-derived here for the same reason as
`algorithmRun`: no compiled interface of the K4 module is available. It carries no mathematical
content of its own. -/
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

/-! ## The local-global collection -/

-- `localSteps` and `localValue` are families *labelled* by the index: the binder `v` is part of the
-- declared shape even where the type on the right does not consume it (`∀ v, ℕ → ℚ_[3]` and
-- `∀ v, ℚ_[3]`). The unused-variable linter is therefore off around the structure below, so that the
-- fields keep exactly the names and binder shapes stated in the task; it is switched back on at once.
set_option linter.unusedVariables false

/-- **A local-global collection with execution provenance at every local piece, and one global
reading.**

This is the set-level shape of `⊼lc-gl` as recorded in `h1-decision.md`, §结论二 (local objects, one
global object, localisation between them), with `Fin n` in place of the places of a number field. The
intended reading of each field:

* `localInput`, `mem` — the `n` local inputs, each in the principal-unit domain of the logarithm;
* `localSteps`, `steps_eq` — the local trace **is** `algorithmRun (localInput v)`, by definitional
  equality. As in K4 this is the field that carries provenance: without it a trace could be any
  sequence, e.g. a constant one, and `converges` would then certify an arbitrary value;
* `localValue`, `converges` — each local reading is the limit of that local trace;
* `globalValue`, `localization` — one global reading, tied to the local ones by
  `globalValue = localValue v` for all `v`.

**The `localization` field is a toy stand-in.** In the source the localisation data are morphisms
between genuinely different objects with a compatibility structure; here it is the single equation
"the global reading is the common local reading", the crudest relation of the required shape. It is not
IUT's localisation. See the module docstring.

Nothing here mentions IUT, and no field is a landing condition: `localValue` lies in
`CoreTransport.logImage ℚ_[3]` only as a *theorem* (`localValue_mem_logImage`). -/
structure LocalGlobalCollection (n : ℕ) where
  /-- The `n` local inputs. -/
  localInput : Fin n → ℚ_[3]
  /-- Each local input lies in the principal-unit domain of the logarithm series. -/
  mem : ∀ v, ‖localInput v - 1‖ < 1
  /-- The trace of the local execution at each index, step by step. -/
  localSteps : ∀ v, ℕ → ℚ_[3]
  /-- Each local trace **is** the algorithm at that local input, by definitional equality. -/
  steps_eq : ∀ v, localSteps v = algorithmRun (localInput v)
  /-- The local reading at each index. -/
  localValue : ∀ v, ℚ_[3]
  /-- Each local reading is the limit of the corresponding local trace. -/
  converges : ∀ v, Filter.Tendsto (localSteps v) Filter.atTop (𝓝 (localValue v))
  /-- The global reading. -/
  globalValue : ℚ_[3]
  /-- **Toy localisation**: the global reading is the common local reading. Not IUT's localisation. -/
  localization : ∀ v, globalValue = localValue v

set_option linter.unusedVariables true

/-- The provenance field, read as a single statement: the collection's trace function *is* the
algorithm applied to the collection's input function. `funext` of `steps_eq`, no more. -/
theorem localSteps_eq_algorithm (c : LocalGlobalCollection n) :
    c.localSteps = fun v => algorithmRun (c.localInput v) :=
  funext c.steps_eq

/-! ## Provenance determines the reading -/

/-- **Provenance determines each local reading.** The local reading at `v` is the limit of the local
trace; the trace is the algorithm at `localInput v`; the algorithm's partial sums converge to
`CoreTransport.localLog (localInput v)` by the quoted theorem; the limit is unique.

The three ingredients are `converges v` (the limit statement), `steps_eq v` (the trace is the
algorithm) and `hasSum_logTerm_localLog` (the library's convergence theorem). Which way the dependency
runs matters: the reading is *forced* by the trace, and the trace is forced by the algorithm and the
input. The proof cannot be reproduced with a constant trace, because `steps_eq v` would then have to
prove a constant sequence equal to `algorithmRun (c.localInput v)`. -/
theorem localValue_determined (c : LocalGlobalCollection n) (v : Fin n) :
    c.localValue v = CoreTransport.localLog (c.localInput v) := by
  -- the trace, being the algorithm, converges to the local reading the structure records
  have hrun : Tendsto (algorithmRun (c.localInput v)) Filter.atTop (𝓝 (c.localValue v)) := by
    rw [← c.steps_eq v]
    exact c.converges v
  have hsteps : Tendsto
      (fun m : ℕ => ∑ k ∈ Finset.range m, PadicLogVolume.logTerm (c.localInput v) k)
      Filter.atTop (𝓝 (c.localValue v)) := by
    simpa only [algorithmRun_eq_partialSums] using hrun
  -- the same partial sums converge to `localLog`, by the existing Q_3 theorem
  have hlog : Tendsto
      (fun m : ℕ => ∑ k ∈ Finset.range m, PadicLogVolume.logTerm (c.localInput v) k)
      Filter.atTop (𝓝 (CoreTransport.localLog (c.localInput v))) :=
    (hasSum_logTerm_localLog (c.mem v)).tendsto_sum_nat
  exact tendsto_nhds_unique hsteps hlog

/-- **Provenance determines the whole local reading function**, not one component: the reading is
`CoreTransport.localLog` composed with the collection's input function. -/
theorem localValues_determined (c : LocalGlobalCollection n) :
    c.localValue = fun v => CoreTransport.localLog (c.localInput v) :=
  funext fun v => localValue_determined c v

/-- **Provenance determines the global reading, at any chosen index.** The toy localisation identifies
the global reading with the local one, and the local one is already forced. -/
theorem globalValue_determined_at (c : LocalGlobalCollection n) (v : Fin n) :
    c.globalValue = CoreTransport.localLog (c.localInput v) := by
  rw [c.localization v, localValue_determined c v]

/-- **Provenance determines the global reading**, stated for `n ≥ 1` in the form `Fin (n + 1)`, with
the index `0` used for the toy localisation.

The `Fin (n + 1)` shape is a choice, made to state the requirement without an extra
`[NeZero n]`-style hypothesis: `0 : Fin (n + 1)` needs no side condition. The general form
`globalValue_determined_at` is stronger — it holds at *every* index and for every `n` — and this
theorem is its specialisation. -/
theorem globalValue_determined {n : ℕ} (c : LocalGlobalCollection (n + 1)) :
    c.globalValue = CoreTransport.localLog (c.localInput 0) :=
  globalValue_determined_at c 0

/-- **Two collections with the same inputs have the same reading**, local function and global value
alike. This is the collection-level form of K4's `value_unique`, and it is what fixes the boundary of
the anti-degeneracy statements below: a separation between two readings can only come from data the
provenance-typed reading actually consumes, namely the inputs. -/
theorem both_readings_unique {n : ℕ} {c₁ c₂ : LocalGlobalCollection n}
    (h : c₁.localInput = c₂.localInput) (v : Fin n) :
    c₁.localValue = c₂.localValue ∧ c₁.globalValue = c₂.globalValue := by
  constructor
  · funext u
    rw [localValue_determined c₁ u, localValue_determined c₂ u, h]
  · rw [globalValue_determined_at c₁ v, globalValue_determined_at c₂ v, h]

/-! ## Landing is a consequence of provenance, not a substitute for it -/

/-- **Landing, as a consequence rather than a condition.** Each local reading lies in the
principal-unit log image `CoreTransport.logImage ℚ_[3]`.

This is deliberately *not* a field of `LocalGlobalCollection`: it follows from
`localValue_determined`, i.e. from the fact that the reading is the algorithm's limit at a
principal-unit input. It is recorded to make the contrast with the audited interfaces explicit — there
the analogous statement is a structure field (`EtaAlg.realisation`), i.e. a landing condition, and a
landing condition alone can never determine a value. See `logImage_Q3_eq_closedBall` for how weak that
condition is. -/
theorem localValue_mem_logImage (c : LocalGlobalCollection n) (v : Fin n) :
    c.localValue v ∈ CoreTransport.logImage ℚ_[3] :=
  ⟨c.localInput v, c.mem v, (localValue_determined c v).symm⟩

/-- **The landing predicate on a collection**: every local reading lies in the log image. This is the
collection-level analogue of a `realisation` field; here it is a predicate, proved of every collection
by `landing_of_provenance`. -/
def SatisfiesLanding {n : ℕ} (c : LocalGlobalCollection n) : Prop :=
  ∀ v, c.localValue v ∈ CoreTransport.logImage ℚ_[3]

/-- **Every collection satisfies the landing predicate**, as a theorem. So the predicate constrains
nothing about the readings — which is the point of the two separation statements below. -/
theorem landing_of_provenance (c : LocalGlobalCollection n) : SatisfiesLanding c :=
  fun v => localValue_mem_logImage c v

/-- **Why a landing condition cannot replace provenance.** The principal-unit log image of `ℚ_[3]` is
the whole closed ball of radius `‖3‖ = 1/3`, not a single point: membership in it is satisfied by an
entire ball of values, so it can never pin down which value an execution produced.

This is the same statement as in K4 and in `DelegatedLogBridge`, obtained here from
`CoreLog.principal_unit_log_image` through the definition-level identification of the two literal
series (`localLog_eq_padicLog`). -/
theorem logImage_Q3_eq_closedBall :
    CoreTransport.logImage ℚ_[3] = {y : ℚ_[3] | ‖y‖ ≤ (3 : ℝ)⁻¹} := by
  unfold CoreTransport.logImage
  rw [show (CoreTransport.localLog : ℚ_[3] → ℚ_[3]) = PadicLogVolume.padicLog from
    funext localLog_eq_padicLog]
  exact CoreLog.principal_unit_log_image

/-! ## Concrete computations used to separate two readings -/

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`. -/
theorem norm_four_sub_one : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- `-2` is a principal unit of `ℚ_[3]`: `‖-2 - 1‖ = ‖-3‖ = 1/3 < 1`. -/
theorem norm_neg_two_sub_one : ‖(-2 : ℚ_[3]) - 1‖ < 1 := by
  have h : (-2 : ℚ_[3]) - 1 = -3 := by norm_num
  rw [h, norm_neg]
  exact CoreLog.norm_three_lt_one

/-- `1` is a principal unit of `ℚ_[3]`: `‖1 - 1‖ = 0 < 1`. -/
theorem norm_one_sub_one : ‖(1 : ℚ_[3]) - 1‖ < 1 := by
  have h : (1 : ℚ_[3]) - 1 = 0 := by norm_num
  rw [h, norm_zero]
  norm_num

/-- `‖2‖ = 1` in `ℚ_[3]`, since `2` is prime to `3`. -/
theorem norm_two_Q3 : ‖(2 : ℚ_[3])‖ = 1 :=
  PadicLogVolume.norm_two_eq_one (p := 3) (by decide) CoreLog.norm_three_lt_one (by decide)

/-- `‖2 * 3‖ = ‖3‖ = 1/3`, so `3` sits inside the ball of radius `‖2p‖` on which the remainder
estimate `PadicLogVolume.norm_logRem_le` applies. -/
theorem norm_two_mul_three : ‖(2 : ℚ_[3]) * 3‖ = (3 : ℝ)⁻¹ := by
  rw [norm_mul, norm_two_Q3, one_mul, CoreLog.norm_three]

/-- `‖3‖ ≤ ‖2 * 3‖`, the hypothesis shape required by `PadicLogVolume.norm_logRem_le`. -/
theorem norm_three_le_two_mul_three : ‖(3 : ℚ_[3])‖ ≤ ‖(2 : ℚ_[3]) * 3‖ := by
  rw [CoreLog.norm_three, norm_two_mul_three]

/-- **The remainder estimate at `a = 3`.** `‖logRem 3‖ ≤ ‖3‖ * ‖3‖ = 1/9`, from the existing
contraction estimate for the remainder `log (1 + a) - a`. -/
theorem norm_logRem_three_le : ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (9 : ℝ)⁻¹ := by
  have h := PadicLogVolume.norm_logRem_le (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (3 : ℚ_[3])) norm_three_le_two_mul_three
  have h' : ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := by
    simpa only [Nat.cast_ofNat, CoreLog.norm_three] using h
  calc ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := h'
    _ = (9 : ℝ)⁻¹ := by norm_num

/-- The same estimate at `a = -3`, which is the input `-2 = 1 + (-3)`. -/
theorem norm_logRem_neg_three_le : ‖PadicLogVolume.logRem (-3 : ℚ_[3])‖ ≤ (9 : ℝ)⁻¹ := by
  have h := PadicLogVolume.norm_logRem_le (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (-3 : ℚ_[3])) (by rw [norm_neg]; exact norm_three_le_two_mul_three)
  have h' : ‖PadicLogVolume.logRem (-3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := by
    simpa only [Nat.cast_ofNat, norm_neg, CoreLog.norm_three] using h
  calc ‖PadicLogVolume.logRem (-3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := h'
    _ = (9 : ℝ)⁻¹ := by norm_num

/-- `localLog 1 = 0`, since every term of the series at `1` vanishes. -/
theorem localLog_one : CoreTransport.localLog (1 : ℚ_[3]) = 0 := by
  rw [localLog_eq_padicLog]
  exact PadicLogVolume.padicLog_one

/-- **`localLog` at `4 = 1 + 3`, split off its linear part**: `log 4 = 3 + logRem 3`, from the
existing rearrangement `PadicLogVolume.padicLog_one_add`. -/
theorem localLog_four :
    CoreTransport.localLog (4 : ℚ_[3]) = 3 + PadicLogVolume.logRem (3 : ℚ_[3]) := by
  rw [localLog_eq_padicLog]
  have h4 : (4 : ℚ_[3]) = 1 + 3 := by norm_num
  rw [h4]
  exact PadicLogVolume.padicLog_one_add (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (3 : ℚ_[3])) CoreLog.norm_three_lt_one

/-- **`localLog` at `-2 = 1 + (-3)`**: `log (-2) = -3 + logRem (-3)`. -/
theorem localLog_neg_two :
    CoreTransport.localLog (-2 : ℚ_[3]) = -3 + PadicLogVolume.logRem (-3 : ℚ_[3]) := by
  rw [localLog_eq_padicLog]
  have h2 : (-2 : ℚ_[3]) = 1 + (-3) := by norm_num
  rw [h2]
  exact PadicLogVolume.padicLog_one_add (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (-3 : ℚ_[3])) (by rw [norm_neg]; exact CoreLog.norm_three_lt_one)

/-- **`localLog 4 ≠ 0`.** If it were zero, the remainder `logRem 3 = log 4 - 3` would equal `-3`,
whose norm is `1/3`; but `‖logRem 3‖ ≤ 1/9`. So `localLog 4` is a nonzero point of the log image. -/
theorem localLog_four_ne_zero : CoreTransport.localLog (4 : ℚ_[3]) ≠ 0 := by
  intro h
  have h1 : PadicLogVolume.logRem (3 : ℚ_[3]) = -(3 : ℚ_[3]) := by
    rw [localLog_four] at h
    linear_combination h
  have h2 : ‖(3 : ℚ_[3])‖ ≤ (9 : ℝ)⁻¹ := by
    have h3 := norm_logRem_three_le
    rw [h1, norm_neg] at h3
    exact h3
  rw [CoreLog.norm_three] at h2
  norm_num at h2

/-- **`localLog 4 ≠ localLog (-2)`.** The two readings differ by `6` up to two remainders of norm at
most `1/9` each, and `‖6‖ = 1/3 > 1/9 + 1/9`. Both inputs are principal units other than `1`, so this
separates two *nontrivial* points of the same log image. -/
theorem localLog_four_ne_localLog_negTwo :
    CoreTransport.localLog (4 : ℚ_[3]) ≠ CoreTransport.localLog (-2 : ℚ_[3]) := by
  intro h
  have h1 : PadicLogVolume.logRem (3 : ℚ_[3]) = CoreTransport.localLog (4 : ℚ_[3]) - 3 := by
    rw [localLog_four]
    ring
  have h2 : PadicLogVolume.logRem (-3 : ℚ_[3]) = CoreTransport.localLog (-2 : ℚ_[3]) + 3 := by
    rw [localLog_neg_two]
    ring
  have hdiff : (-6 : ℚ_[3]) =
      PadicLogVolume.logRem (3 : ℚ_[3]) - PadicLogVolume.logRem (-3 : ℚ_[3]) := by
    rw [h1, h2, h]
    ring
  have hnorm : ‖(-6 : ℚ_[3])‖ ≤ (9 : ℝ)⁻¹ + (9 : ℝ)⁻¹ := by
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_logRem_three_le, norm_logRem_neg_three_le]
  have hsix : ‖(-6 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by
    have h6 : (-6 : ℚ_[3]) = -((2 : ℚ_[3]) * 3) := by norm_num
    rw [h6, norm_neg, norm_two_mul_three]
  rw [hsix] at hnorm
  norm_num at hnorm

/-! ## Non-vacuity: three collections -/

/-- **A collection with `n = 1` at the input `4`**, with the genuine trace `algorithmRun 4` and the
reading it forces. Every field is discharged by an actual proof: `mem` by `norm_four_sub_one`,
`steps_eq` by `rfl` (definitional equality with the algorithm), `converges` by the quoted convergence
theorem composed with `algorithmRun_eq_partialSums`, `localization` by `rfl`. -/
def witnessFour : LocalGlobalCollection 1 where
  localInput := fun _ => 4
  mem := fun _ => norm_four_sub_one
  localSteps := fun _ => algorithmRun 4
  steps_eq := fun _ => rfl
  localValue := fun _ => CoreTransport.localLog 4
  converges := fun _ => by
    rw [algorithmRun_eq_partialSums]
    exact (hasSum_logTerm_localLog norm_four_sub_one).tendsto_sum_nat
  globalValue := CoreTransport.localLog 4
  localization := fun _ => rfl

/-- **A collection with `n = 1` at the input `-2`**, same shape as `witnessFour`. -/
def witnessNegTwo : LocalGlobalCollection 1 where
  localInput := fun _ => -2
  mem := fun _ => norm_neg_two_sub_one
  localSteps := fun _ => algorithmRun (-2)
  steps_eq := fun _ => rfl
  localValue := fun _ => CoreTransport.localLog (-2)
  converges := fun _ => by
    rw [algorithmRun_eq_partialSums]
    exact (hasSum_logTerm_localLog norm_neg_two_sub_one).tendsto_sum_nat
  globalValue := CoreTransport.localLog (-2)
  localization := fun _ => rfl

/-- **A collection with `n = 1` at the input `1`**, whose reading is `log 1 = 0`. -/
def witnessOne : LocalGlobalCollection 1 where
  localInput := fun _ => 1
  mem := fun _ => norm_one_sub_one
  localSteps := fun _ => algorithmRun 1
  steps_eq := fun _ => rfl
  localValue := fun _ => CoreTransport.localLog 1
  converges := fun _ => by
    rw [algorithmRun_eq_partialSums]
    exact (hasSum_logTerm_localLog norm_one_sub_one).tendsto_sum_nat
  globalValue := CoreTransport.localLog 1
  localization := fun _ => rfl

/-- Non-vacuity at the type itself: `LocalGlobalCollection 1` is inhabited by an actual collection. -/
example : LocalGlobalCollection 1 := witnessFour

/-! ## Anti-degeneracy: the landing condition does not determine the global reading -/

/-- **The point of the file.** Two collections *with the same `n`* (`n = 1`), each of whose local
readings lands in `CoreTransport.logImage ℚ_[3]` — so both satisfy the landing predicate, by
`landing_of_provenance` — and whose **global readings differ**.

The landing predicate contains no information that could separate them: it says only "the reading lies
in the log image", and both readings do. Provenance, by contrast, separates them immediately, because
it fixes each reading to be the limit of the algorithm at its own input, and the two inputs give
different readings (`localLog_four_ne_zero`, with `localLog 1 = 0`). So a landing condition is not a
substitute for provenance at the level of a collection either.

This is the preferred form of the anti-degeneracy statement, and it is *not* obstructed by the toy's
`localization` field: that field constrains the global reading of a *single* collection against its own
local readings, and says nothing about two different collections. What the toy does rule out is
"same inputs, different readings", which is exactly `both_readings_unique`. -/
theorem landing_does_not_determine_global :
    ∃ c₁ c₂ : LocalGlobalCollection 1,
      SatisfiesLanding c₁ ∧ SatisfiesLanding c₂ ∧ c₁.globalValue ≠ c₂.globalValue := by
  refine ⟨witnessFour, witnessOne, landing_of_provenance _, landing_of_provenance _, ?_⟩
  show CoreTransport.localLog (4 : ℚ_[3]) ≠ CoreTransport.localLog (1 : ℚ_[3])
  rw [localLog_one]
  exact localLog_four_ne_zero

/-- The same separation with **both** inputs nontrivial: `4` and `-2` are principal units different
from `1`, and their readings differ (`localLog_four_ne_localLog_negTwo`). So the failure above is not an
artefact of using the trivial input `1`; it persists between two genuine, nonzero points of the log
image. -/
theorem landing_does_not_determine_global_nontrivial :
    ∃ c₁ c₂ : LocalGlobalCollection 1,
      SatisfiesLanding c₁ ∧ SatisfiesLanding c₂ ∧ c₁.globalValue ≠ c₂.globalValue := by
  refine ⟨witnessFour, witnessNegTwo, landing_of_provenance _, landing_of_provenance _, ?_⟩
  show CoreTransport.localLog (4 : ℚ_[3]) ≠ CoreTransport.localLog (-2 : ℚ_[3])
  exact localLog_four_ne_localLog_negTwo

end

end CollectionProvenance

#print axioms CollectionProvenance.algorithmRun
#print axioms CollectionProvenance.algorithmRun_eq_partialSums
#print axioms CollectionProvenance.localLog_eq_padicLog
#print axioms CollectionProvenance.hasSum_logTerm_localLog
#print axioms CollectionProvenance.localSteps_eq_algorithm
#print axioms CollectionProvenance.localValue_determined
#print axioms CollectionProvenance.localValues_determined
#print axioms CollectionProvenance.globalValue_determined_at
#print axioms CollectionProvenance.globalValue_determined
#print axioms CollectionProvenance.both_readings_unique
#print axioms CollectionProvenance.localValue_mem_logImage
#print axioms CollectionProvenance.SatisfiesLanding
#print axioms CollectionProvenance.landing_of_provenance
#print axioms CollectionProvenance.logImage_Q3_eq_closedBall
#print axioms CollectionProvenance.norm_four_sub_one
#print axioms CollectionProvenance.norm_neg_two_sub_one
#print axioms CollectionProvenance.norm_one_sub_one
#print axioms CollectionProvenance.norm_two_Q3
#print axioms CollectionProvenance.norm_two_mul_three
#print axioms CollectionProvenance.norm_three_le_two_mul_three
#print axioms CollectionProvenance.norm_logRem_three_le
#print axioms CollectionProvenance.norm_logRem_neg_three_le
#print axioms CollectionProvenance.localLog_one
#print axioms CollectionProvenance.localLog_four
#print axioms CollectionProvenance.localLog_neg_two
#print axioms CollectionProvenance.localLog_four_ne_zero
#print axioms CollectionProvenance.localLog_four_ne_localLog_negTwo
#print axioms CollectionProvenance.witnessFour
#print axioms CollectionProvenance.witnessNegTwo
#print axioms CollectionProvenance.witnessOne
#print axioms CollectionProvenance.landing_does_not_determine_global
#print axioms CollectionProvenance.landing_does_not_determine_global_nontrivial
