import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W2 upgrade: compatible transitions on a chain of presentations, and the reading they force

**This file is a toy province, and nothing more.** W2 (`candidates/core-transport/CollectionProvenance.lean`)
put execution provenance on a *collection*, but wired the global reading to the local ones by a single
equation, `globalValue = localValue v`. That equation is a **toy equality**: it is the crudest relation of
the required shape, and it says that a collection's pieces agree *because they are literally the same
value*. Actual local-global data does not have that shape: its pieces are related by **transitions** —
isomorphisms between genuinely different presentations of one object — and a reading attached to those
pieces is well defined only when the transitions are **compatible** (a cocycle/composition law). This
file replaces the toy equality by compatible transitions and proves that a compatible chain forces a
single reading, while an incompatible one does not.

**Why the obligation is exactly this.** `research/core-backward-2026-10-23/h1-decision.md`, §结论一′,
quotes the source (txt lines 8869–8873) defining `n,◦HT^{D-Θ±ellNF}` as the Hodge theater "determined,
**up to isomorphism**, by the various `n,m`-theaters". An object determined only up to isomorphism has no
canonical presentation: a reading built from a *chosen* presentation is a reading of the presentation and
not of the object, unless it is proved independent of that choice. §结论一′ also records that the relevant
indeterminacy is an **orbit** (full poly-isomorphism, h1-coricity.md), so the invariance to be modelled is
invariance across a family of presentations connected by isomorphisms — which is what the transition data
below are. Nothing here asserts that this obligation is discharged for the real object; it exhibits the
shape and proves it on one concrete case.

**The model, on `ℚ_[3]`.** One object, `k ≥ 1` presentations of it, indexed by `Fin k`:

* `input i` — the presentation at index `i`, a principal unit `‖input i - 1‖ < 1` of `ℚ_[3]`;
* `step i j h` — the **transition** from presentation `i` to presentation `j` (`i ≤ j`), a *function*
  `ℚ_[3] → ℚ_[3]`, namely multiplication by the principal unit `unit i j h`. Transitions are thus
  isomorphisms of the multiplicative structure of the principal units, with inverse `stepInv`; this is
  not an equality of inputs (`step_eq`, `stepInv_step`);
* `step_input` — the **elementary** transitions really carry the presentation forward:
  `step i (i+1) (input i) = input (i+1)`. This is what makes the `input i` presentations *of one object*;
* `IsCompatible c` — the **cocycle law**: for `i ≤ j ≤ l`, `unit i l = unit i j * unit j l`, i.e. the
  transition recorded for the pair `(i,l)` equals the two steps composed. It is a *hypothesis* of the main
  theorem, not a field of the structure: an arbitrary chain of presentations-with-transitions need not
  satisfy it, and `chainBroken` below does not.

**The reading.** The reading at presentation `i` is `localLog` of the presentation's input transported
**back to the base frame** by the inverse transition from the base to `i`
(`relativeInput i = stepInv (base) i (input i)`). It is computed from the actual data at `i` — the input
there and the transition recorded there — and it is a genuine limit, not a fiat value: `reading_hasSum`
and `reading_is_limit_of_algorithm` show it is the sum, and the limit of the partial sums
`algorithmRun`, of a series that converges at that argument (`relativeInput_mem`). Note that it is *not*
defined as `localLog` of a fixed point; that it nevertheless equals a fixed value on a compatible chain is
the theorem `reading_eq_base`, not the definition.

**What is proved.**
* `input_transport` — on a compatible chain the elementary transports accumulate to the recorded
  comparison transition: `input i = input (base) * unit (base) i`. This is the induction where the
  cocycle law is used, one step at a time.
* `reading_eq_base`, `reading_compatible` — on a compatible chain every reading equals the base reading,
  hence all readings agree. This is the upgrade of W2's toy equality: agreement is now a *consequence* of
  the transition data, not an equation imposed on the values.
* `chainCompat` — a compatible chain with explicit numbers (`4, 16, 64 = 4^1, 4^2, 4^3`, units `4^{j-i}`),
  whose readings are all `localLog 4` (`chainCompat_reading`).
* `chainBroken` — the same inputs and the same elementary units, but the recorded direct transition
  `0 → 2` is `4^3 = 64` instead of `4^2 = 16`. It is **not** compatible
  (`chainBroken_not_compatible`) and its readings differ: `localLog 4` at `0` against `localLog 1 = 0` at
  `2` (`chainBroken_readings_differ`). This is the anti-degeneracy statement, with explicit numbers and a
  concrete witness chain, not a negated universal.
* `difference_lies_in_the_direct_transition` — the two chains have the *same* presentations and the *same*
  elementary transitions; only the recorded comparison transition `0 → 2` differs. So the disagreement of
  the readings is produced by the transition data alone, which is precisely the feature the toy equality
  of W2 had no room for.

**A design point, stated because it is the whole content of item 4.** On the principal units of `ℚ_[3]`
multiplication is *sharply* transitive, and the logarithm is injective there. Hence if the model required
**every** transition to transport the presentation (`step i j (input i) = input j` for all `i ≤ j`), the
comparison units would be determined by the inputs (`unit i j = input j / input i`), the cocycle law would
hold automatically, and every reading would be equal *by construction* — the anti-degeneracy statement
would then be impossible, not merely hard, and no theorem would be left to prove. The model therefore
keeps two sorts of transition data, as the source's localisation data does: the elementary transports that
tie consecutive presentations together (a field, `step_input`), and the comparison transitions from the
base to each presentation (recorded data, `unit (base) i`), whose agreement with the elementary ones is
exactly the cocycle hypothesis. The reading consumes the comparison transition; compatibility is what
makes it independent of the presentation. Nothing here is hidden: `IsCompatible` is stated in full and the
witness of its failure is concrete.

**What this file does not establish.** It says nothing about IUT's localisation data: not about `⊼fQ₁`,
`⊼fQ₂`, the formal quotient `⊼fQ₂ modulo ⊼fQ₁` of §结论二, log-volumes, log-shells, Θ-links, `Ism`,
Corollary 3.12, Hodge theaters, coricity, poly-isomorphisms, Galois actions, prime-strips or Frobenioids.
`Fin k` is a set of indices, not the set of places of a number field; the transitions here are
multiplication by powers of `4` on `ℚ_[3]`, not localisation morphisms; and the logarithm series on
`ℚ_[3]` is not the η-algorithm. In particular the file does **not** show that any reading of the real
object is presentation-independent, and it is not evidence for or against any IUT claim. What it shows is
that the obligation of §结论一′ has a formally checkable shape — reading invariant under a compatible
family of transitions, not under an equality of values — and that in that shape the invariance has a real
hypothesis: drop it and the readings separate, with explicit numbers.

**Why the pieces are restated rather than imported.** `CollectionProvenance.lean`,
`ExecutionProvenance.lean` and `ReadingInvariance.lean` are top-level modules of the package: `lakefile.lean`
declares a single library, `lean_lib CoreTransport`, whose modules are those under `CoreTransport/`, so
those three files are not Lake targets, no `olean` of them exists, and `import CollectionProvenance` is not
available. `algorithmRun`, `localLog_eq_padicLog` and `hasSum_logTerm_localLog` are therefore restated with
the same statements, exactly as the W-files before this one each did, so that this file depends on
`CoreTransport.Basic` and `CoreLog.QpThree` alone. They carry no new mathematics: the first is the
p-adic logarithm's partial-sum algorithm (not the η-algorithm of IUT), the second identifies two literal
series by unfolding both definitions, and the third is `CoreLog.principal_unit_log_hasSum` quoted.
`localLog_four_ne_zero` is likewise restated from W2, together with the remainder estimates it needs
(`norm_logRem_three_le`), since it is the only separation of two readings used below.

Series conventions: the term is the one already used by `CoreTransport.localLog` and by
`PadicLogVolume.logTerm`; convergence on principal units is the existing
`CoreLog.principal_unit_log_hasSum`, quoted rather than re-proved. The `ℚ_[3]` norm facts
(`norm_pow_sub_one_lt`, `norm_inv_sub_one_lt`, `mul_inv_cancel₀`) are used as they stand.

A dependency-footprint block at the end of the file records, for every declaration below, that the only
dependencies are `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace TransitionCompatibility

noncomputable section

open Filter Topology

/-! ## 1. The algorithm, the two literal series, and the quoted convergence theorem -/

/-- **The genuine finite algorithm, re-stated.** The `n`-th partial sum of the logarithm series at `x`,
with the same term `(-1)^k (x-1)^(k+1)/(k+1)` as `CoreTransport.localLog`. This is the p-adic
logarithm's partial-sum algorithm on `ℚ_[3]`, *not* the η-algorithm of IUT; it is repeated here only
because `ExecutionProvenance.lean` is not a Lake target and has no compiled interface (see the module
docstring). Being a plain definition it binds the traces below by definitional equality, not by a
hypothesis. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the existing series term,
definitionally. This is the bridge from a trace to the library's convergence theorem; it adds no content
of its own. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- `CoreTransport.localLog` and `PadicLogVolume.padicLog` are the same series, written twice; this
records that in the open by unfolding both definitions. It is not mathematical content, and no later
claim rests on the two being secretly different objects. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **The existing convergence result, quoted.** For `‖x - 1‖ < 1` the series sums to
`CoreTransport.localLog x`; the proof goes through `CoreLog.principal_unit_log_summable`, so it depends on
the genuine p-adic convergence argument and not on `tsum`'s totalised default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact CoreLog.principal_unit_log_hasSum hx

/-! ## 2. Chains of presentations with transitions -/

/-- The base index `0` of a chain, written out so that no `OfNat`/`LT` instance search is involved.
A chain needs at least one presentation, hence the `NeZero k` binder on `PresentationChain`. -/
def base (k : ℕ) [NeZero k] : Fin k := ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩

/-- The base index is below every index: this is what lets every reading be taken in the frame of the
base presentation. -/
theorem base_le {k : ℕ} [NeZero k] (i : Fin k) : (base k).val ≤ i.val := Nat.zero_le i.val

/-- **A chain of presentations of one object, with transitions between them.**

The intended reading of each field:

* `input`, `mem` — the presentation at each index, a principal unit of `ℚ_[3]`;
* `step`, `unit`, `unit_mem`, `step_eq` — the transition from presentation `i` to presentation `j`
  (`i ≤ j`) is the function `y ↦ y * unit i j h`, i.e. multiplication by a principal unit. It is a
  function between presentations, not an equality of inputs; its inverse is `stepInv`, and
  `stepInv_step` proves the two compose to the identity;
* `unit_refl` — the identity transition is multiplication by `1`;
* `step_input` — the **elementary** transition `i → i+1` really carries the presentation at `i` to the
  presentation at `i+1`. This is the field that ties the `input i` together into presentations of a
  single object.

The **comparison** transitions `unit (base) i` are recorded data, not derived from the inputs; requiring
them to agree with the elementary ones is the cocycle law `IsCompatible`, which is a hypothesis of the main
theorem and fails for `chainBroken`. See the module docstring for why the model keeps the two sorts of
transition data apart: on the principal units multiplication is sharply transitive, so had every transition
been required to transport the presentation, the comparison units would be forced by the inputs and the
cocycle law would hold automatically. -/
structure PresentationChain (k : ℕ) [NeZero k] where
  /-- The presentation at each index. -/
  input : Fin k → ℚ_[3]
  /-- Each presentation is a principal unit, i.e. in the domain of the logarithm series. -/
  mem : ∀ i, ‖input i - 1‖ < 1
  /-- The transition from presentation `i` to presentation `j`, as a function on `ℚ_[3]`. -/
  step : ∀ i j : Fin k, i.val ≤ j.val → ℚ_[3] → ℚ_[3]
  /-- The principal unit by which that transition acts. -/
  unit : ∀ i j : Fin k, i.val ≤ j.val → ℚ_[3]
  /-- Every transition unit is a principal unit. -/
  unit_mem : ∀ (i j : Fin k) (h : i.val ≤ j.val), ‖unit i j h - 1‖ < 1
  /-- A transition *is* multiplication by its unit: a function, not an equation on inputs. -/
  step_eq : ∀ (i j : Fin k) (h : i.val ≤ j.val) (y : ℚ_[3]), step i j h y = y * unit i j h
  /-- The identity transition is multiplication by `1`. -/
  unit_refl : ∀ (i : Fin k) (h : i.val ≤ i.val), unit i i h = 1
  /-- The elementary transition carries the presentation at `i` to the one at `i + 1`. -/
  step_input : ∀ (i : Fin k) (h : i.val + 1 < k),
    step i ⟨i.val + 1, h⟩ (Nat.le_succ i.val) (input i) = input ⟨i.val + 1, h⟩

/-- The inverse of a transition: multiplication by the inverse unit. Together with `stepInv_step` this
makes every transition an isomorphism of the principal units, which is the sense in which it is a
transition between presentations rather than a mere comparison of values. -/
def PresentationChain.stepInv {k : ℕ} [NeZero k] (c : PresentationChain k) (i j : Fin k)
    (h : i.val ≤ j.val) : ℚ_[3] → ℚ_[3] :=
  fun y => y * (c.unit i j h)⁻¹

/-- **The presentation at `i`, transported back to the base frame.** This is the actual data the reading
consumes: the input at `i`, pushed back along the inverse of the recorded transition from the base to
`i`. It is not `localLog` of a fixed point, and it is not the base input by definition — that it coincides
with the base input on a compatible chain is `input_transport`. -/
def PresentationChain.relativeInput {k : ℕ} [NeZero k] (c : PresentationChain k) (i : Fin k) :
    ℚ_[3] :=
  c.stepInv (base k) i (base_le i) (c.input i)

/-- **The reading at presentation `i`**: the logarithm of the presentation transported back to the base
frame. It is defined from the data at `i` alone; `reading_hasSum` and `reading_is_limit_of_algorithm`
identify it with a convergent series and with the limit of the algorithm's partial sums, and
`reading_eq_base` proves it is presentation-independent on a compatible chain. -/
def PresentationChain.reading {k : ℕ} [NeZero k] (c : PresentationChain k) (i : Fin k) : ℚ_[3] :=
  CoreTransport.localLog (c.relativeInput i)

/-- **The cocycle (compatibility) law**: for `i ≤ j ≤ l`, the transition recorded for `(i,l)` is the
composite of the transitions recorded for `(i,j)` and `(j,l)`. This is the hypothesis under which the
reading is presentation-independent (`reading_compatible`). It is *not* a field of the structure, and an
arbitrary chain need not satisfy it: `chainBroken` does not. -/
def IsCompatible {k : ℕ} [NeZero k] (c : PresentationChain k) : Prop :=
  ∀ (i j l : Fin k) (hij : i.val ≤ j.val) (hjl : j.val ≤ l.val),
    c.unit i l (hij.trans hjl) = c.unit i j hij * c.unit j l hjl

/-! ## 3. The reading is a genuine limit, and it is forced on a compatible chain -/

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`. This is the input at the base
presentation of both concrete chains below. -/
theorem norm_four_sub_one : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- **The transported presentation is still in the domain of the logarithm.** Transition units are
principal units and inverse principal units are principal units, so the product is one; hence the reading
at every index is the sum of a convergent series and not a totalised default. -/
theorem PresentationChain.relativeInput_mem {k : ℕ} [NeZero k] (c : PresentationChain k)
    (i : Fin k) : ‖c.relativeInput i - 1‖ < 1 := by
  have hinv := PadicLogVolume.norm_inv_sub_one_lt (c.unit_mem (base k) i (base_le i))
  exact PadicLogVolume.norm_mul_sub_one_lt (c.mem i) hinv

/-- **The reading is the sum of a convergent series** at the transported presentation: provenance, in the
sense of K4/W2, for the chain. -/
theorem PresentationChain.reading_hasSum {k : ℕ} [NeZero k] (c : PresentationChain k)
    (i : Fin k) : HasSum (PadicLogVolume.logTerm (c.relativeInput i)) (c.reading i) :=
  hasSum_logTerm_localLog (c.relativeInput_mem i)

/-- **The reading is the limit of the algorithm's partial sums** at the transported presentation, so it is
the value of an actual execution and not a chosen number. -/
theorem PresentationChain.reading_is_limit_of_algorithm {k : ℕ} [NeZero k]
    (c : PresentationChain k) (i : Fin k) :
    Tendsto (algorithmRun (c.relativeInput i)) atTop (𝓝 (c.reading i)) := by
  rw [algorithmRun_eq_partialSums]
  exact (c.reading_hasSum i).tendsto_sum_nat

/-- **Transitions are isomorphisms**: the inverse transition undoes the transition, on all of `ℚ_[3]`.
The hypothesis-free form is possible because a transition unit is a principal unit and hence nonzero. -/
theorem PresentationChain.stepInv_step {k : ℕ} [NeZero k] (c : PresentationChain k) (i j : Fin k)
    (h : i.val ≤ j.val) (y : ℚ_[3]) : c.stepInv i j h (c.step i j h y) = y := by
  have hu : c.unit i j h ≠ 0 := PadicLogVolume.ne_zero_of_norm_sub_one_lt (c.unit_mem i j h)
  rw [PresentationChain.stepInv, c.step_eq i j h y, mul_assoc, mul_inv_cancel₀ hu, mul_one]

/-- **On a compatible chain the elementary transports accumulate to the recorded comparison transition**:
`input i = input (base) * unit (base) i`. This is an induction on the index in which the cocycle law is used
once per step; it is the only place where the hypothesis `IsCompatible` is consumed, and it is what turns
"the transitions compose" into a statement about the presentations themselves. -/
theorem input_transport_aux {k : ℕ} [NeZero k] (c : PresentationChain k) (hc : IsCompatible c) :
    ∀ n (hn : n < k),
      c.input ⟨n, hn⟩ = c.input (base k) * c.unit (base k) ⟨n, hn⟩ (base_le ⟨n, hn⟩) := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hb : (⟨0, hn⟩ : Fin k) = base k := rfl
    rw [hb, c.unit_refl (base k) (base_le (base k)), mul_one]
  | succ m ih =>
    intro hn
    have hm : m < k := by omega
    have hstep : c.step ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) (c.input ⟨m, hm⟩) =
        c.input ⟨m + 1, hn⟩ :=
      c.step_input ⟨m, hm⟩ hn
    have hmul : c.step ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) (c.input ⟨m, hm⟩)
        = c.input ⟨m, hm⟩ * c.unit ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) :=
      c.step_eq _ _ _ _
    have hcoc := hc (base k) ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.zero_le m) (Nat.le_succ m)
    calc c.input ⟨m + 1, hn⟩
        = c.step ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) (c.input ⟨m, hm⟩) := by rw [hstep]
      _ = c.input ⟨m, hm⟩ * c.unit ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) := hmul
      _ = (c.input (base k) * c.unit (base k) ⟨m, hm⟩ (base_le ⟨m, hm⟩))
            * c.unit ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m) := by rw [ih hm]
      _ = c.input (base k) * (c.unit (base k) ⟨m, hm⟩ (base_le ⟨m, hm⟩)
            * c.unit ⟨m, hm⟩ ⟨m + 1, hn⟩ (Nat.le_succ m)) := by rw [mul_assoc]
      _ = c.input (base k) * c.unit (base k) ⟨m + 1, hn⟩ (base_le ⟨m + 1, hn⟩) := by rw [← hcoc]

/-- **The accumulated transport**, at every index: the presentation at `i` is the base presentation
transported by the recorded comparison transition `base → i`. -/
theorem input_transport {k : ℕ} [NeZero k] (c : PresentationChain k) (hc : IsCompatible c)
    (i : Fin k) : c.input i = c.input (base k) * c.unit (base k) i (base_le i) :=
  input_transport_aux c hc i.val i.isLt

/-- **The reading of a compatible chain is the base reading.** The transported presentation
`relativeInput i` collapses to the base input by `input_transport`, so the reading at `i` is `localLog` of
one and the same value for every `i`. -/
theorem reading_eq_base {k : ℕ} [NeZero k] (c : PresentationChain k) (hc : IsCompatible c)
    (i : Fin k) : c.reading i = CoreTransport.localLog (c.input (base k)) := by
  have hu : c.unit (base k) i (base_le i) ≠ 0 :=
    PadicLogVolume.ne_zero_of_norm_sub_one_lt (c.unit_mem _ _ _)
  have hrel : c.relativeInput i = c.input (base k) := by
    rw [PresentationChain.relativeInput, PresentationChain.stepInv, input_transport c hc i,
      mul_assoc, mul_inv_cancel₀ hu, mul_one]
  rw [PresentationChain.reading, hrel]

/-- **The point of the file: on a compatible chain the reading does not depend on the presentation.**
This is what W2's toy equality was standing in for: there, agreement of the readings was a field of the
structure; here it is a theorem, derived from the cocycle law through `input_transport`, and it is false
without that law (`chainBroken_readings_differ`). -/
theorem reading_compatible {k : ℕ} [NeZero k] (c : PresentationChain k) (hc : IsCompatible c) :
    ∀ i j : Fin k, c.reading i = c.reading j := by
  intro i j
  rw [reading_eq_base c hc i, reading_eq_base c hc j]

/-! ## 4. `localLog 4 ≠ 0`: the one separation of readings used below

Restated from W2's `CollectionProvenance.lean` (which is not a Lake target, see the module docstring). The
argument is the existing remainder estimate for `log (1 + a) - a`: at `a = 3` the remainder has norm at most
`1/9`, so `log 4 = 3 + logRem 3` cannot be `0`, since that would make `logRem 3 = -3` of norm `1/3`. -/

/-- `‖2‖ = 1` in `ℚ_[3]`, since `2` is prime to `3`. -/
theorem norm_two_Q3 : ‖(2 : ℚ_[3])‖ = 1 :=
  PadicLogVolume.norm_two_eq_one (p := 3) (by decide) CoreLog.norm_three_lt_one (by decide)

/-- `‖2 * 3‖ = ‖3‖ = 1/3`. -/
theorem norm_two_mul_three : ‖(2 : ℚ_[3]) * 3‖ = (3 : ℝ)⁻¹ := by
  rw [norm_mul, norm_two_Q3, one_mul, CoreLog.norm_three]

/-- `‖3‖ ≤ ‖2 * 3‖`, the hypothesis shape required by `PadicLogVolume.norm_logRem_le`. -/
theorem norm_three_le_two_mul_three : ‖(3 : ℚ_[3])‖ ≤ ‖(2 : ℚ_[3]) * 3‖ := by
  rw [CoreLog.norm_three, norm_two_mul_three]

/-- **The remainder estimate at `a = 3`**: `‖logRem 3‖ ≤ ‖3‖ * ‖3‖ = 1/9`, from the existing contraction
estimate for the remainder `log (1 + a) - a`. -/
theorem norm_logRem_three_le : ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (9 : ℝ)⁻¹ := by
  have h := PadicLogVolume.norm_logRem_le (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (3 : ℚ_[3])) norm_three_le_two_mul_three
  have h' : ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := by
    simpa only [Nat.cast_ofNat, CoreLog.norm_three] using h
  calc ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := h'
    _ = (9 : ℝ)⁻¹ := by norm_num

/-- `localLog 1 = 0`, since every term of the series at `1` vanishes. -/
theorem localLog_one : CoreTransport.localLog (1 : ℚ_[3]) = 0 := by
  rw [localLog_eq_padicLog]
  exact PadicLogVolume.padicLog_one

/-- **`localLog` at `4 = 1 + 3`, split off its linear part**: `log 4 = 3 + logRem 3`, from the existing
rearrangement `PadicLogVolume.padicLog_one_add`. -/
theorem localLog_four :
    CoreTransport.localLog (4 : ℚ_[3]) = 3 + PadicLogVolume.logRem (3 : ℚ_[3]) := by
  rw [localLog_eq_padicLog]
  have h4 : (4 : ℚ_[3]) = 1 + 3 := by norm_num
  rw [h4]
  exact PadicLogVolume.padicLog_one_add (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (3 : ℚ_[3])) CoreLog.norm_three_lt_one

/-- **`localLog 4 ≠ 0`.** If it were zero, the remainder `logRem 3 = log 4 - 3` would equal `-3`, whose
norm is `1/3`; but `‖logRem 3‖ ≤ 1/9`. This is the numeric fact that separates the two readings of
`chainBroken`. -/
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

/-! ## 5. Two concrete three-presentation chains

Both chains have the same three presentations, `4, 16, 64 = 4^1, 4^2, 4^3`, and the same elementary
transitions `i → i+1` (multiplication by `4`). They differ in exactly one comparison transition: from the
base `0` to `2`, the compatible chain records `4^2 = 16` and the other records `4^3 = 64`. -/

/-- The index `0` of a three-presentation chain, written out so that no instance search is involved. -/
def i0 : Fin 3 := ⟨0, by decide⟩

/-- The index `1`. -/
def i1 : Fin 3 := ⟨1, by decide⟩

/-- The index `2`. -/
def i2 : Fin 3 := ⟨2, by decide⟩

/-- The exponent of the transition unit in the compatible chain: the unit of the transition `i → j` is
`4 ^ (j - i)`, which is exactly `input j / input i`. -/
def expCompat (i j : ℕ) : ℕ := j - i

/-- The exponent in the incompatible chain: with `d = j - i` it is `d + d / 2`, which is `d` for the
elementary transitions (`d = 1`, and also `d = 0`) and `d + 1 = 3` for the comparison transition `0 → 2`
(`d = 2`). So the two chains share their presentations and all their elementary transitions, and differ only
in the single comparison transition from the base `0` to `2`. -/
def expBroken (i j : ℕ) : ℕ := j - i + (j - i) / 2

/-- `‖4 ^ n - 1‖ < 1` for every `n`: every power of `4` is a principal unit. This is the existing
`PadicLogVolume.norm_pow_sub_one_lt` at `x = 4`, and it discharges both the `mem` fields and the
`unit_mem` fields of the two chains below. -/
theorem norm_four_pow_sub_one (n : ℕ) : ‖(4 : ℚ_[3]) ^ n - 1‖ < 1 :=
  PadicLogVolume.norm_pow_sub_one_lt norm_four_sub_one n

/-- **A compatible chain**: three presentations `4, 16, 64`, transitions acting by `4 ^ (j - i)`. The
cocycle law holds because `(j - i) + (l - j) = l - i` for `i ≤ j ≤ l`. -/
def chainCompat : PresentationChain 3 where
  input := fun i => (4 : ℚ_[3]) ^ (i.val + 1)
  mem := fun i => norm_four_pow_sub_one (i.val + 1)
  step := fun i j _ y => y * (4 : ℚ_[3]) ^ (expCompat i.val j.val)
  unit := fun i j _ => (4 : ℚ_[3]) ^ (expCompat i.val j.val)
  unit_mem := fun _ _ _ => norm_four_pow_sub_one _
  step_eq := fun _ _ _ _ => rfl
  unit_refl := fun i _ => by
    show (4 : ℚ_[3]) ^ expCompat i.val i.val = 1
    rw [expCompat, Nat.sub_self, pow_zero]
  step_input := fun i _ => by
    have hsub : i.val + 1 - i.val = 1 := by omega
    show (4 : ℚ_[3]) ^ (i.val + 1) * (4 : ℚ_[3]) ^ expCompat i.val (i.val + 1)
      = (4 : ℚ_[3]) ^ (i.val + 1 + 1)
    rw [expCompat, hsub, pow_one, ← pow_succ]

/-- **The incompatible chain**: same presentations and same elementary transitions as `chainCompat`, but
the comparison transition `0 → 2` is recorded as `4 ^ 3 = 64` instead of `4 ^ 2 = 16`. -/
def chainBroken : PresentationChain 3 where
  input := fun i => (4 : ℚ_[3]) ^ (i.val + 1)
  mem := fun i => norm_four_pow_sub_one (i.val + 1)
  step := fun i j _ y => y * (4 : ℚ_[3]) ^ (expBroken i.val j.val)
  unit := fun i j _ => (4 : ℚ_[3]) ^ (expBroken i.val j.val)
  unit_mem := fun _ _ _ => norm_four_pow_sub_one _
  step_eq := fun _ _ _ _ => rfl
  unit_refl := fun i _ => by
    have hexp : expBroken i.val i.val = 0 := by norm_num [expBroken]
    show (4 : ℚ_[3]) ^ expBroken i.val i.val = 1
    rw [hexp, pow_zero]
  step_input := fun i _ => by
    have hexp : expBroken i.val (i.val + 1) = 1 := by norm_num [expBroken]
    show (4 : ℚ_[3]) ^ (i.val + 1) * (4 : ℚ_[3]) ^ expBroken i.val (i.val + 1)
      = (4 : ℚ_[3]) ^ (i.val + 1 + 1)
    rw [hexp, pow_one, ← pow_succ]

/-- Non-vacuity at the type itself: `PresentationChain 3` is inhabited by an actual chain. -/
example : PresentationChain 3 := chainCompat

/-- **The compatible chain satisfies the cocycle law.** With `4 ^ (j - i)` as the unit, the composite is
`4 ^ ((j - i) + (l - j)) = 4 ^ (l - i)`, which is the direct unit. -/
theorem chainCompat_isCompatible : IsCompatible chainCompat := by
  intro i j l hij hjl
  show (4 : ℚ_[3]) ^ expCompat i.val l.val
      = (4 : ℚ_[3]) ^ expCompat i.val j.val * (4 : ℚ_[3]) ^ expCompat j.val l.val
  rw [expCompat, expCompat, expCompat, ← pow_add]
  congr 1
  omega

/-- **The compatible chain is compatible.** So the hypothesis of `reading_compatible` is satisfiable by an
actual chain, and the theorem below is not vacuous. -/
theorem chainCompat_readings_agree (i j : Fin 3) : chainCompat.reading i = chainCompat.reading j :=
  reading_compatible chainCompat chainCompat_isCompatible i j

/-- **Every reading of the compatible chain is `localLog 4`**, the reading of the base presentation. -/
theorem chainCompat_reading (i : Fin 3) : chainCompat.reading i = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [reading_eq_base chainCompat chainCompat_isCompatible i]
  have hbase : chainCompat.input (base 3) = (4 : ℚ_[3]) := by
    simp [chainCompat, base]
  rw [hbase]

/-! ## 6. Anti-degeneracy: an incompatible chain whose readings differ -/

/-- The comparison unit `0 → 2` of the compatible chain is `4 ^ 2 = 16`. -/
theorem chainCompat_unit_02 (h : (i0).val ≤ (i2).val) : chainCompat.unit i0 i2 h = 16 := by
  norm_num [chainCompat, i0, i2, expCompat]

/-- The comparison unit `0 → 2` of the broken chain is `4 ^ 3 = 64`. -/
theorem chainBroken_unit_02 (h : (i0).val ≤ (i2).val) : chainBroken.unit i0 i2 h = 64 := by
  norm_num [chainBroken, i0, i2, expBroken]

/-- The elementary unit `0 → 1` of the broken chain is `4 ^ 1 = 4`, the same value as in the compatible
chain. -/
theorem chainBroken_unit_01 (h : (i0).val ≤ (i1).val) : chainBroken.unit i0 i1 h = 4 := by
  norm_num [chainBroken, i0, i1, expBroken]

/-- The elementary unit `1 → 2` of the broken chain is `4 ^ 1 = 4`. -/
theorem chainBroken_unit_12 (h : (i1).val ≤ (i2).val) : chainBroken.unit i1 i2 h = 4 := by
  norm_num [chainBroken, i1, i2, expBroken]

/-- **The broken chain is not compatible.** At `(0,1,2)` the cocycle law would read `4 ^ 3 = 4 ^ 1 * 4 ^ 1`,
i.e. `64 = 16`, which is false. Note that the failure is at a *comparison* transition: the elementary
transitions `0 → 1 → 2` are the correct ones. -/
theorem chainBroken_not_compatible : ¬ IsCompatible chainBroken := by
  intro hc
  have h := hc i0 i1 i2 (by decide) (by decide)
  rw [chainBroken_unit_02, chainBroken_unit_01, chainBroken_unit_12] at h
  norm_num at h

/-- The transported presentation at `0` of the broken chain is `4`: the base transition is the identity. -/
theorem chainBroken_relativeInput_zero : chainBroken.relativeInput i0 = 4 := by
  have hi : chainBroken.input i0 = (4 : ℚ_[3]) := by
    norm_num [chainBroken, i0]
  have hu : chainBroken.unit (base 3) i0 (base_le i0) = 1 := by
    norm_num [chainBroken, base, i0, expBroken]
  rw [PresentationChain.relativeInput, PresentationChain.stepInv, hi, hu]
  simp

/-- The transported presentation at `2` of the broken chain is `1`: the recorded transition `0 → 2` is
`64`, which cancels the input `64` there. -/
theorem chainBroken_relativeInput_two : chainBroken.relativeInput i2 = 1 := by
  have hi : chainBroken.input i2 = (4 : ℚ_[3]) ^ 3 := by
    norm_num [chainBroken, i2]
  have hu : chainBroken.unit (base 3) i2 (base_le i2) = (4 : ℚ_[3]) ^ 3 := by
    norm_num [chainBroken, base, i2, expBroken]
  rw [PresentationChain.relativeInput, PresentationChain.stepInv, hi, hu]
  exact mul_inv_cancel₀
    (pow_ne_zero 3 (PadicLogVolume.ne_zero_of_norm_sub_one_lt norm_four_sub_one))

/-- The reading at `0` of the broken chain is `localLog 4`. -/
theorem chainBroken_reading_zero : chainBroken.reading i0 = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [PresentationChain.reading, chainBroken_relativeInput_zero]

/-- **The reading at `2` of the broken chain is `0`**, i.e. `localLog 1`: the recorded transition `0 → 2`
transporting `64` back gives `1`, and `localLog 1 = 0`. -/
theorem chainBroken_reading_two : chainBroken.reading i2 = 0 := by
  rw [PresentationChain.reading, chainBroken_relativeInput_two, localLog_one]

/-- **Anti-degeneracy, with explicit numbers: the readings of the incompatible chain differ.**
`chainBroken.reading i0 = localLog 4` and `chainBroken.reading i2 = 0`, and `localLog 4 ≠ 0`
(`localLog_four_ne_zero`). This is a concrete witness chain, not a negated universal: the presentations
are `4, 16, 64`, the elementary transitions multiply by `4`, and the single comparison transition `0 → 2`
records `64` instead of `16`. -/
theorem chainBroken_readings_differ : chainBroken.reading i0 ≠ chainBroken.reading i2 := by
  rw [chainBroken_reading_zero, chainBroken_reading_two]
  exact localLog_four_ne_zero

/-- **The difference between the two chains lies in one comparison transition only.** They have the same
presentations (`rfl`) and the same elementary transitions (both are `4 ^ 1 = 4`, for every `i`), and they
disagree only at the comparison transition `0 → 2` (`16` against `64`). Together with
`chainBroken_readings_differ` this pins down where the disagreement of the readings comes from: the
transition data, not the presentations — the very distinction the toy equality of W2 could not express. -/
theorem difference_lies_in_the_direct_transition :
    chainBroken.input = chainCompat.input ∧
      (∀ (i : Fin 3) (h : i.val + 1 < 3),
        chainBroken.unit i ⟨i.val + 1, h⟩ (Nat.le_succ i.val)
          = chainCompat.unit i ⟨i.val + 1, h⟩ (Nat.le_succ i.val)) ∧
      chainBroken.unit i0 i2 (by decide) ≠ chainCompat.unit i0 i2 (by decide) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i h
    have hb : expBroken i.val (i.val + 1) = 1 := by norm_num [expBroken]
    have hc : expCompat i.val (i.val + 1) = 1 := by norm_num [expCompat]
    have h1 : chainBroken.unit i ⟨i.val + 1, h⟩ (Nat.le_succ i.val) = (4 : ℚ_[3]) := by
      norm_num [chainBroken, hb]
    have h2 : chainCompat.unit i ⟨i.val + 1, h⟩ (Nat.le_succ i.val) = (4 : ℚ_[3]) := by
      norm_num [chainCompat, hc]
    rw [h1, h2]
  · rw [chainBroken_unit_02, chainCompat_unit_02]
    norm_num

/-- **The anti-degeneracy statement of the file, existentially stated**: there is a chain whose
transitions fail the cocycle law and whose readings differ. The witness is `chainBroken`, whose readings at
`0` and `2` are `localLog 4` and `0`. -/
theorem exists_incompatible_chain_with_differing_readings :
    ∃ c : PresentationChain 3, ¬ IsCompatible c ∧ c.reading i0 ≠ c.reading i2 :=
  ⟨chainBroken, chainBroken_not_compatible, chainBroken_readings_differ⟩

end

end TransitionCompatibility

#print axioms TransitionCompatibility.algorithmRun
#print axioms TransitionCompatibility.algorithmRun_eq_partialSums
#print axioms TransitionCompatibility.localLog_eq_padicLog
#print axioms TransitionCompatibility.hasSum_logTerm_localLog
#print axioms TransitionCompatibility.base
#print axioms TransitionCompatibility.base_le
#print axioms TransitionCompatibility.PresentationChain
#print axioms TransitionCompatibility.PresentationChain.stepInv
#print axioms TransitionCompatibility.PresentationChain.relativeInput
#print axioms TransitionCompatibility.PresentationChain.reading
#print axioms TransitionCompatibility.IsCompatible
#print axioms TransitionCompatibility.PresentationChain.relativeInput_mem
#print axioms TransitionCompatibility.PresentationChain.reading_hasSum
#print axioms TransitionCompatibility.PresentationChain.reading_is_limit_of_algorithm
#print axioms TransitionCompatibility.PresentationChain.stepInv_step
#print axioms TransitionCompatibility.input_transport_aux
#print axioms TransitionCompatibility.input_transport
#print axioms TransitionCompatibility.reading_eq_base
#print axioms TransitionCompatibility.reading_compatible
#print axioms TransitionCompatibility.norm_four_sub_one
#print axioms TransitionCompatibility.norm_two_Q3
#print axioms TransitionCompatibility.norm_two_mul_three
#print axioms TransitionCompatibility.norm_three_le_two_mul_three
#print axioms TransitionCompatibility.norm_logRem_three_le
#print axioms TransitionCompatibility.localLog_one
#print axioms TransitionCompatibility.localLog_four
#print axioms TransitionCompatibility.localLog_four_ne_zero
#print axioms TransitionCompatibility.i0
#print axioms TransitionCompatibility.i1
#print axioms TransitionCompatibility.i2
#print axioms TransitionCompatibility.expCompat
#print axioms TransitionCompatibility.expBroken
#print axioms TransitionCompatibility.norm_four_pow_sub_one
#print axioms TransitionCompatibility.chainCompat
#print axioms TransitionCompatibility.chainBroken
#print axioms TransitionCompatibility.chainCompat_isCompatible
#print axioms TransitionCompatibility.chainCompat_readings_agree
#print axioms TransitionCompatibility.chainCompat_reading
#print axioms TransitionCompatibility.chainCompat_unit_02
#print axioms TransitionCompatibility.chainBroken_unit_02
#print axioms TransitionCompatibility.chainBroken_unit_01
#print axioms TransitionCompatibility.chainBroken_unit_12
#print axioms TransitionCompatibility.chainBroken_not_compatible
#print axioms TransitionCompatibility.chainBroken_relativeInput_zero
#print axioms TransitionCompatibility.chainBroken_relativeInput_two
#print axioms TransitionCompatibility.chainBroken_reading_zero
#print axioms TransitionCompatibility.chainBroken_reading_two
#print axioms TransitionCompatibility.chainBroken_readings_differ
#print axioms TransitionCompatibility.difference_lies_in_the_direct_transition
#print axioms TransitionCompatibility.exists_incompatible_chain_with_differing_readings
-- audit completion (main line): the four below were declared in the file but absent from the
-- report list, so the first strict check flagged them as un-audited. No proof was changed.
#print axioms TransitionCompatibility.PresentationChain.stepInv_step
#print axioms TransitionCompatibility.PresentationChain.relativeInput_mem
#print axioms TransitionCompatibility.PresentationChain.reading_hasSum
#print axioms TransitionCompatibility.PresentationChain.reading_is_limit_of_algorithm
