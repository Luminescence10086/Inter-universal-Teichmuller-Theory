import CoreTransport.Basic
import CoreLog.QpThree

/-!
# W6: the reading descends to the quotient — `SameObject` as an equivalence relation, and
`Quotient.lift` of the reading

**This file is a toy province and nothing more.** W4 (`candidates/core-transport/TransitionCompatibility.lean`)
proved that on a chain of presentations whose transitions satisfy the cocycle law, the reading is *constant*:
`reading_compatible : ∀ i j, reading i = reading j`. That is one half of the invariance obligation. The other
half — the one this file supplies — is that the constancy is not a statement *about the chain* but a statement
*about the object*: the transition data must induce an **equivalence relation** on the presentations ("these
two presentations describe the same object"), and the reading must be a function **on the quotient**,
recovered by `Quotient.lift`, with the descended function computing the original values
(`descendedReading_mk`). "Constant on the chain" is a comparison of values indexed by `Fin k`; "descends to
the quotient" says the reading is the *pullback of a function on the isomorphism classes*, which is what a
reading of an object determined only up to isomorphism actually has to be, and which additionally makes the
descent **unique** (`descendedReading_unique`) — a statement that has no analogue at the level of the chain.

**Why the obligation exists.** `research/core-backward-2026-10-23/h1-coricity.md` records the source's
determination of `n,◦HT^{D-Θ±ellNF}` "up to isomorphism" (txt 8869–8873 via Theorem 1.5(i), 2881–2889) and
the definition of a poly-isomorphism as an **orbit of isomorphisms** (txt 2005–2007); the invariance therefore
has to hold on the orbit, i.e. on the classes of an equivalence relation, not on a chosen chain of
representatives. A chain of presentations with transitions is the toy stand-in for such an orbit.

**The model, restated from W4 (which is not importable: see below).** One object, `k ≥ 1` presentations of it,
indexed by `Fin k`:

* `input i` — the presentation at `i`, a principal unit `‖input i - 1‖ < 1` of `ℚ_[3]`;
* `step i j h` — the transition from `i` to `j` (`i ≤ j`), multiplication by the principal unit `unit i j h`,
  with inverse `stepInv` (`stepInv_step`); this is a function between presentations, not an equality of inputs;
* `step_input` — the **elementary** transitions carry the presentation forward: `step i (i+1) (input i) =
  input (i+1)`;
* `IsCompatible c` — the **cocycle law** `unit i l = unit i j * unit j l` for `i ≤ j ≤ l`; a hypothesis, not a
  field, and `chainBroken` below does not satisfy it;
* `reading i` — `localLog` of the presentation at `i` transported back to the frame of the base presentation
  (`relativeInput i`), a genuine limit of the algorithm `algorithmRun` (`reading_hasSum`,
  `reading_is_limit_of_algorithm`), not a fiat value.

**What this file adds.**

1. **`SameObject c i j`** — "presentations `i` and `j` describe the same object" — is defined *from the
   transition data only*: `SameObjectStep c a b` holds when the recorded transition between `a` and `b`
   (whichever of the two directions is defined) actually transports the presentation,
   `input a * unit a b h = input b`; and `SameObject` is its reflexive–transitive closure.

2. **Why the closure is taken, and why that is not a dodge.** The structure records a unit only for ordered
   pairs `i ≤ j` and imposes no relation between `unit a b` and `unit b a`, so the one-step relation is *not*
   transitively closed in mixed directions as it stands; the honest construction of the quotient of a
   non-transitive relation is its closure. What is then proved is that **on a compatible chain the closure is
   redundant**: `sameObjectStep_direct` shows that compatible transitions make every pair of presentations
   related in **one** step, so `SameObject` is the one-step relation there and transitivity is inherited from
   the cocycle law (`sameObjectStep_of_compatible` is the transported-presentation identity that produces the
   single edge).

3. **The quotient.** `sameObject_equivalence`, `sameObjectSetoid`, and
   `descendedReading c hc : Quotient (sameObjectSetoid c) → ℚ_[3] := Quotient.lift (reading c) _`, whose
   obligation `SameObject c a b → reading a = reading b` is `sameObject_reading_eq`. The proof is genuinely
   *per step*: `reading_eq_of_transport` shows that one correct transition plus the cocycle law at the base
   frame gives `relativeInput a = relativeInput b`, and `sameObjectStep_reading` + induction on the closure
   give the constancy. So the cocycle law is consumed twice over, and at two different places: it produces the
   single edges (`sameObjectStep_of_compatible`) and it makes each edge preserve the reading
   (`reading_eq_of_transport`). `descendedReading_mk` is the required computation rule; `descendedReading_const`
   evaluates the descended function on the concrete chain; `descendedReading_unique` shows the descent is the
   only such function on the quotient.

4. **Anti-degeneracy, with explicit numbers (two chains of three presentations, `4, 16, 64 = 4^1, 4^2, 4^3`,
   identical except in the recorded comparison transition `0 → 2`).**
   * `chainCompat` (`unit i j = 4^(j-i)`, compatible): the comparison transition `0 → 2` is `4^2 = 16` and
     `4 * 16 = 64 = input 2`, so `0` and `2` are related in **one** step (`chainCompat_transport_02`); all
     readings are `localLog 4`.
   * `chainBroken` (`unit 0 2` recorded as `4^3 = 64`): now `4 * 64 = 256 ≠ 64`, so there is **no** one-step
     relation between `0` and `2` (`chainBroken_no_direct_edge`) — the one-step relation is strictly smaller —
     **but** the elementary transitions are untouched, so `SameObject chainBroken i1 i2` still holds
     (`chainBroken_sameObject_one_two`) and `SameObject chainBroken i0 i2` holds in two steps
     (`chainBroken_sameObject`). And the readings there are `chainBroken.reading i1 = localLog 4` against
     `chainBroken.reading i2 = 0` (`chainBroken_readings_one_two_differ`, separated by `localLog_four_ne_zero`).
     Hence the lift's constancy hypothesis **fails** on `chainBroken` (`constancy_not_universal_on_broken`) and
     consequently **no** function on the quotient computes the readings there
     (`no_factorization_on_broken`: there is no `f` with `f ⟦i⟧ = reading i` for all `i`).
   * Which of item 6's two alternatives is proved: **both**, and neither is impossible here. They are not
     impossible precisely because `SameObject` is built from the transition data and never mentions `reading`,
     so it can relate two indices whose readings differ. Had `SameObject` been defined as, say, equality of
     `relativeInput`, the constancy obligation would hold by `congrArg` and the anti-degeneracy would be
     vacuous; that is the trap this definition avoids, and it is why the relation is the transition-carried one.

5. **An honest limitation, stated rather than hidden.** In this model `step_input` is a *field*, so consecutive
   presentations are same-object on **every** chain, and hence `SameObject` is total on every chain
   (`sameObject_total`) — the quotient is a subsingleton (`sameObject_quotient_subsingleton`) for `chainCompat`
   and `chainBroken` alike. So the quotient's *shape* cannot distinguish the two chains; what distinguishes
   them is whether the reading is constant on it, i.e. whether the descent exists at all. That is exactly the
   content of item 6, and it is also the honest limit of the toy: a model in which several objects occur (so
   that the quotient has more than one point) would need the elementary transports to be *data that can fail*,
   which would in turn make the reading's very definition moot. The toy can therefore exhibit the descent and
   its failure, but not a non-trivial quotient — and that limit is recorded here rather than papered over.

**Restated rather than imported.** `TransitionCompatibility.lean`, `ReadingInvariance.lean`,
`CollectionProvenance.lean` and `ExecutionProvenance.lean` are top-level modules of the package: `lakefile.lean`
declares a single library, `lean_lib CoreTransport`, whose modules are those under `CoreTransport/`, so those
files are not Lake targets, no `olean` of them exists, and `import TransitionCompatibility` is unavailable.
Everything used from W4 is therefore restated below with the same statements: `algorithmRun`,
`algorithmRun_eq_partialSums`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`, the chain structure, the
reading, `IsCompatible`, `input_transport`, `reading_eq_base`, `reading_compatible`, the two concrete chains
and the `localLog 4 ≠ 0` separation with its remainder estimates. None of these restatements carries new
mathematics; the new declarations are items 1–4 above plus their corollaries.

Series conventions: the term is the one already used by `CoreTransport.localLog` and by
`PadicLogVolume.logTerm`; convergence on principal units is the existing `CoreLog.principal_unit_log_hasSum`,
quoted rather than re-proved.

**What this file does not establish.** It says nothing about IUT's localisation data: not about `⊼fQ₁`,
`⊼fQ₂`, the formal quotient `⊼fQ₂ modulo ⊼fQ₁`, log-volumes, log-shells, Θ-links, `Ism`, Corollary 3.12,
Hodge theaters, coricity, poly-isomorphisms, Galois actions, prime-strips or Frobenioids. `Fin k` is a set of
indices, not the set of places of a number field; the transitions are multiplication by powers of `4` on
`ℚ_[3]`, not localisation morphisms; the logarithm series is not the η-algorithm; `SameObject` is not an
`Ism`. Nothing here shows that any reading of the real object is presentation-independent, and nothing here is
evidence for or against any IUT claim. What is shown is that the invariance obligation has the shape of a
*descent*: transition data induce an equivalence relation, the reading factors through the quotient, and the
factorisation can fail — with explicit numbers — when the cocycle law is dropped.

A dependency-footprint block at the end records, for every declaration below, that the only dependencies are
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ReadingFactorization

noncomputable section

open Filter Topology

/-! ## 1. The algorithm, the two literal series, and the quoted convergence theorem -/

/-- **The genuine finite algorithm, re-stated.** The `n`-th partial sum of the logarithm series at `x`, with
the same term `(-1)^k (x-1)^(k+1)/(k+1)` as `CoreTransport.localLog`. This is the p-adic logarithm's
partial-sum algorithm on `ℚ_[3]`, *not* the η-algorithm of IUT; it is repeated here only because the W-files
are not Lake targets and have no compiled interface (see the module docstring). Being a plain definition it
binds the traces below by definitional equality, not by a hypothesis. -/
def algorithmRun (x : ℚ_[3]) (n : ℕ) : ℚ_[3] :=
  ∑ k ∈ Finset.range n, (-1 : ℚ_[3]) ^ k * (x - 1) ^ (k + 1) / (k + 1)

/-- The algorithm's `n`-th partial sum *is* the `n`-th partial sum of the existing series term,
definitionally: the bridge from a trace to the library's convergence theorem. It adds no content of its own. -/
theorem algorithmRun_eq_partialSums (x : ℚ_[3]) :
    algorithmRun x = fun n : ℕ => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k := by
  funext n
  rfl

/-- `CoreTransport.localLog` and `PadicLogVolume.padicLog` are the same series, written twice; recorded in the
open by unfolding both definitions. It is not mathematical content. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **The existing convergence result, quoted.** For `‖x - 1‖ < 1` the series sums to
`CoreTransport.localLog x`; the proof goes through `CoreLog.principal_unit_log_summable`, so it depends on the
genuine p-adic convergence argument and not on `tsum`'s totalised default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact CoreLog.principal_unit_log_hasSum hx

/-! ## 2. Chains of presentations with transitions (W4's design, restated) -/

/-- The base index `0` of a chain, written out so that no `OfNat`/`LT` instance search is involved. -/
def base (k : ℕ) [NeZero k] : Fin k := ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩

/-- The base index is below every index: this is what lets every reading be taken in the frame of the base
presentation. -/
theorem base_le {k : ℕ} [NeZero k] (i : Fin k) : (base k).val ≤ i.val := Nat.zero_le i.val

/-- **A chain of presentations of one object, with transitions between them.**

* `input`, `mem` — the presentation at each index, a principal unit of `ℚ_[3]`;
* `step`, `unit`, `unit_mem`, `step_eq` — the transition from `i` to `j` (`i ≤ j`) is the function
  `y ↦ y * unit i j h`, multiplication by a principal unit; its inverse is `stepInv` (`stepInv_step`);
* `unit_refl` — the identity transition is multiplication by `1`;
* `step_input` — the **elementary** transition really carries the presentation at `i` to the one at `i+1`.

The **comparison** transitions `unit (base) i` are recorded data, not derived from the inputs; requiring them
to agree with the elementary ones is the cocycle law `IsCompatible`, a hypothesis of the main theorems and
false for `chainBroken`. The two sorts of transition data are kept apart because on the principal units of
`ℚ_[3]` multiplication is sharply transitive: had every transition been required to transport the
presentation, the comparison units would be forced by the inputs and compatibility would be automatic. -/
structure Chain (k : ℕ) [NeZero k] where
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

/-- The inverse of a transition: multiplication by the inverse unit. Together with `stepInv_step` this makes
every transition an isomorphism of the principal units. -/
def Chain.stepInv {k : ℕ} [NeZero k] (c : Chain k) (i j : Fin k) (h : i.val ≤ j.val) :
    ℚ_[3] → ℚ_[3] :=
  fun y => y * (c.unit i j h)⁻¹

/-- **The presentation at `i`, transported back to the base frame**: the actual data the reading consumes. -/
def Chain.relativeInput {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) : ℚ_[3] :=
  c.stepInv (base k) i (base_le i) (c.input i)

/-- **The reading at presentation `i`**: the logarithm of the presentation transported back to the base frame.
It is defined from the data at `i` alone; that it is nevertheless presentation-independent on a compatible
chain is the theorem `reading_compatible`, not the definition. -/
def Chain.reading {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) : ℚ_[3] :=
  CoreTransport.localLog (c.relativeInput i)

/-- **The cocycle (compatibility) law**: for `i ≤ j ≤ l` the transition recorded for `(i,l)` is the composite
of those recorded for `(i,j)` and `(j,l)`. This is the hypothesis under which the reading is
presentation-independent (`reading_compatible`) and under which `SameObject` is already one-step
(`sameObjectStep_direct`). It is *not* a field, and `chainBroken` does not satisfy it. -/
def IsCompatible {k : ℕ} [NeZero k] (c : Chain k) : Prop :=
  ∀ (i j l : Fin k) (hij : i.val ≤ j.val) (hjl : j.val ≤ l.val),
    c.unit i l (hij.trans hjl) = c.unit i j hij * c.unit j l hjl

/-! ## 3. The reading is a genuine limit, and it is forced on a compatible chain -/

/-- `4` is a principal unit of `ℚ_[3]`: `‖4 - 1‖ = ‖3‖ = 1/3 < 1`. -/
theorem norm_four_sub_one : ‖(4 : ℚ_[3]) - 1‖ < 1 := by
  have h : (4 : ℚ_[3]) - 1 = 3 := by norm_num
  rw [h]
  exact CoreLog.norm_three_lt_one

/-- **The transported presentation is still in the domain of the logarithm**, so every reading is the sum of a
convergent series and not a totalised default. -/
theorem Chain.relativeInput_mem {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) :
    ‖c.relativeInput i - 1‖ < 1 := by
  have hinv := PadicLogVolume.norm_inv_sub_one_lt (c.unit_mem (base k) i (base_le i))
  exact PadicLogVolume.norm_mul_sub_one_lt (c.mem i) hinv

/-- **The reading is the sum of a convergent series** at the transported presentation. -/
theorem Chain.reading_hasSum {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) :
    HasSum (PadicLogVolume.logTerm (c.relativeInput i)) (c.reading i) :=
  hasSum_logTerm_localLog (c.relativeInput_mem i)

/-- **The reading is the limit of the algorithm's partial sums** at the transported presentation, so it is the
value of an actual execution and not a chosen number. -/
theorem Chain.reading_is_limit_of_algorithm {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) :
    Tendsto (algorithmRun (c.relativeInput i)) atTop (𝓝 (c.reading i)) := by
  rw [algorithmRun_eq_partialSums]
  exact (c.reading_hasSum i).tendsto_sum_nat

/-- **Transitions are isomorphisms**: the inverse transition undoes the transition, on all of `ℚ_[3]`. -/
theorem Chain.stepInv_step {k : ℕ} [NeZero k] (c : Chain k) (i j : Fin k) (h : i.val ≤ j.val)
    (y : ℚ_[3]) : c.stepInv i j h (c.step i j h y) = y := by
  have hu : c.unit i j h ≠ 0 := PadicLogVolume.ne_zero_of_norm_sub_one_lt (c.unit_mem i j h)
  rw [Chain.stepInv, c.step_eq i j h y, mul_assoc, mul_inv_cancel₀ hu, mul_one]

/-- **On a compatible chain the elementary transports accumulate to the recorded comparison transition**:
`input i = input (base) * unit (base) i`. The induction uses the cocycle law once per step. -/
theorem input_transport_aux {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) :
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

/-- **The accumulated transport**, at every index. -/
theorem input_transport {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) (i : Fin k) :
    c.input i = c.input (base k) * c.unit (base k) i (base_le i) :=
  input_transport_aux c hc i.val i.isLt

/-- **The reading of a compatible chain is the base reading.** -/
theorem reading_eq_base {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) (i : Fin k) :
    c.reading i = CoreTransport.localLog (c.input (base k)) := by
  have hu : c.unit (base k) i (base_le i) ≠ 0 :=
    PadicLogVolume.ne_zero_of_norm_sub_one_lt (c.unit_mem _ _ _)
  have hrel : c.relativeInput i = c.input (base k) := by
    rw [Chain.relativeInput, Chain.stepInv, input_transport c hc i, mul_assoc, mul_inv_cancel₀ hu, mul_one]
  rw [Chain.reading, hrel]

/-- **On a compatible chain the reading does not depend on the presentation** (W4's theorem, restated). -/
theorem reading_compatible {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) :
    ∀ i j : Fin k, c.reading i = c.reading j := by
  intro i j
  rw [reading_eq_base c hc i, reading_eq_base c hc j]

/-! ## 4. `localLog 4 ≠ 0`: the one separation of readings used below -/

/-- `‖2‖ = 1` in `ℚ_[3]`, since `2` is prime to `3`. -/
theorem norm_two_Q3 : ‖(2 : ℚ_[3])‖ = 1 :=
  PadicLogVolume.norm_two_eq_one (p := 3) (by decide) CoreLog.norm_three_lt_one (by decide)

/-- `‖2 * 3‖ = ‖3‖ = 1/3`. -/
theorem norm_two_mul_three : ‖(2 : ℚ_[3]) * 3‖ = (3 : ℝ)⁻¹ := by
  rw [norm_mul, norm_two_Q3, one_mul, CoreLog.norm_three]

/-- `‖3‖ ≤ ‖2 * 3‖`, the hypothesis shape required by `PadicLogVolume.norm_logRem_le`. -/
theorem norm_three_le_two_mul_three : ‖(3 : ℚ_[3])‖ ≤ ‖(2 : ℚ_[3]) * 3‖ := by
  rw [CoreLog.norm_three, norm_two_mul_three]

/-- **The remainder estimate at `a = 3`**: `‖logRem 3‖ ≤ 1/9`. -/
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

/-- **`localLog` at `4 = 1 + 3`, split off its linear part**: `log 4 = 3 + logRem 3`. -/
theorem localLog_four :
    CoreTransport.localLog (4 : ℚ_[3]) = 3 + PadicLogVolume.logRem (3 : ℚ_[3]) := by
  rw [localLog_eq_padicLog]
  have h4 : (4 : ℚ_[3]) = 1 + 3 := by norm_num
  rw [h4]
  exact PadicLogVolume.padicLog_one_add (p := 3) (by decide) CoreLog.norm_three_lt_one
    (a := (3 : ℚ_[3])) CoreLog.norm_three_lt_one

/-- **`localLog 4 ≠ 0`.** If it were zero, the remainder `logRem 3 = log 4 - 3` would equal `-3`, of norm
`1/3`; but `‖logRem 3‖ ≤ 1/9`. This is the numeric fact that separates two readings of `chainBroken`. -/
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

/-- `4 ≠ 0` in `ℚ_[3]`: it is a principal unit. Used to cancel it in the concrete computations below. -/
theorem norm_four_ne_zero : (4 : ℚ_[3]) ≠ 0 :=
  PadicLogVolume.ne_zero_of_norm_sub_one_lt norm_four_sub_one

/-! ## 5. `SameObject`: the transition data as a relation on the indices

`SameObject` is *defined from the transition data* and never mentions the reading. That is what makes the
constancy obligation in §6 a real obligation and the anti-degeneracy in §8 possible. -/

/-- **The one-step relation: the recorded transition between `a` and `b` really transports the presentation.**
The structure records a unit only for ordered pairs, so the relation is written with the two possible
orientations; `input a * unit a b h = input b` says that the transition `a → b` (multiplication by
`unit a b h`, by `step_eq`) carries the presentation at `a` to the presentation at `b`. -/
def SameObjectStep {k : ℕ} [NeZero k] (c : Chain k) (a b : Fin k) : Prop :=
  (∃ h : a.val ≤ b.val, c.input a * c.unit a b h = c.input b) ∨
    (∃ h : b.val ≤ a.val, c.input b * c.unit b a h = c.input a)

/-- **`SameObject c i j`: presentations `i` and `j` describe the same object** — the reflexive–transitive
closure of the one-step relation. The closure is taken because the structure records no relation between
`unit a b` and `unit b a`, so the one-step relation need not be transitively closed in mixed orientations;
§5 proves below that on a compatible chain the closure is *redundant* (`sameObjectStep_direct`), i.e. there the
relation is the one-step one. -/
def SameObject {k : ℕ} [NeZero k] (c : Chain k) (i j : Fin k) : Prop :=
  Relation.ReflTransGen (SameObjectStep c) i j

/-- The one-step relation is symmetric: the definition is a disjunction of the two orientations, so swapping
the arguments swaps the disjuncts. No hypothesis is needed. -/
theorem sameObjectStep_symm {k : ℕ} [NeZero k] (c : Chain k) {a b : Fin k}
    (h : SameObjectStep c a b) : SameObjectStep c b a := h.symm

/-- The closure of a symmetric relation is symmetric. This is the only point where the symmetry of
`SameObject` comes from; it is proved by induction on the closure, not quoted, because Mathlib's
`Relation.ReflTransGen` API does not carry a symmetry lemma. -/
theorem reflTransGen_symm {α : Type} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs _ _ hbc) ih

/-- `SameObject` is reflexive: the closure contains the diagonal. -/
theorem sameObject_refl {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) : SameObject c i i :=
  Relation.ReflTransGen.refl

/-- Moreover the diagonal is a *one-step* relation, by the identity-transition field `unit_refl`: so
reflexivity is carried by the transition data and not only by the closure. -/
theorem sameObjectStep_refl {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) : SameObjectStep c i i :=
  Or.inl ⟨Nat.le_refl i.val, by rw [c.unit_refl i (Nat.le_refl i.val), mul_one]⟩

/-- `SameObject` is transitive: the closure is closed under composition. -/
theorem sameObject_trans {k : ℕ} [NeZero k] (c : Chain k) {i j l : Fin k}
    (hij : SameObject c i j) (hjl : SameObject c j l) : SameObject c i l :=
  Relation.ReflTransGen.trans hij hjl

/-- `SameObject` is symmetric. -/
theorem sameObject_symm {k : ℕ} [NeZero k] (c : Chain k) {i j : Fin k}
    (h : SameObject c i j) : SameObject c j i :=
  reflTransGen_symm (fun _ _ => sameObjectStep_symm c) h

/-- **`SameObject` is an equivalence relation.** Note which half needs the compatibility hypothesis: *not*
these three laws, which are structural, but *totality* — on a compatible chain every pair of presentations is
related, and that is `sameObjectStep_direct` below. -/
theorem sameObject_equivalence {k : ℕ} [NeZero k] (c : Chain k) : Equivalence (SameObject c) where
  refl := fun i => sameObject_refl c i
  symm := fun h => sameObject_symm c h
  trans := fun h1 h2 => sameObject_trans c h1 h2

/-- The setoid of presentations up to "describing the same object". Its relation field is `SameObject`
itself; the quotient in §6 is `Quotient (sameObjectSetoid c)`, and `sameObjectSetoid_rfl` records that the
relation is not silently changed by packaging it. -/
def sameObjectSetoid {k : ℕ} [NeZero k] (c : Chain k) : Setoid (Fin k) :=
  Setoid.mk (SameObject c) (sameObject_equivalence c)

/-- The setoid's relation *is* `SameObject`, definitionally: packaging it into a `Setoid` changes nothing, so
the quotient below is the quotient by the relation of §5 and not by some refinement of it. -/
theorem sameObjectSetoid_rfl {k : ℕ} [NeZero k] (c : Chain k) :
    (sameObjectSetoid c).r = SameObject c := rfl

/-- **The elementary transitions are one-step relations on every chain.** This is the field `step_input` read
through `step_eq`; it needs no compatibility, and it is what makes the anti-degeneracy of §8 sharp: the
elementary steps cannot be blamed for the failure there. -/
theorem sameObjectStep_succ {k : ℕ} [NeZero k] (c : Chain k) (i : Fin k) (h : i.val + 1 < k) :
    SameObjectStep c i ⟨i.val + 1, h⟩ := by
  refine Or.inl ⟨Nat.le_succ i.val, ?_⟩
  rw [← c.step_eq i ⟨i.val + 1, h⟩ (Nat.le_succ i.val) (c.input i)]
  exact c.step_input i h

/-- **Compatibility makes one recorded transition the right one.** For `i ≤ j`, the transition recorded for
`(i,j)` transports the presentation at `i` to the presentation at `j`: the base-frame transports of `i` and
`j` differ exactly by `unit i j`, by the cocycle law. This is where the cocycle law is consumed to produce
*edges* of the relation (it is consumed a second time, differently, in `reading_eq_of_transport`). -/
theorem sameObjectStep_of_compatible {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c)
    {i j : Fin k} (h : i.val ≤ j.val) : c.input i * c.unit i j h = c.input j := by
  have hib : c.input i = c.input (base k) * c.unit (base k) i (base_le i) := input_transport c hc i
  have hjb : c.input j = c.input (base k) * c.unit (base k) j (base_le j) := input_transport c hc j
  have hcoc := hc (base k) i j (base_le i) h
  rw [hib, hjb, mul_assoc, ← hcoc]

/-- **On a compatible chain every two presentations are related in one step.** The sharp form of "the closure
is redundant here": no iteration is needed, and the cocycle law is exactly what buys the single edge. -/
theorem sameObjectStep_direct {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) (i j : Fin k) :
    SameObjectStep c i j := by
  rcases le_total i.val j.val with h | h
  · exact Or.inl ⟨h, sameObjectStep_of_compatible c hc h⟩
  · exact Or.inr ⟨h, sameObjectStep_of_compatible c hc h⟩

/-- **Every index is related to the base**, by the elementary transports alone: consecutive steps are
one-step relations (`sameObjectStep_succ`) on *any* chain, compatible or not. -/
theorem sameObject_base_related {k : ℕ} [NeZero k] (c : Chain k) :
    ∀ (n : ℕ) (hn : n < k), SameObject c (base k) ⟨n, hn⟩ := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact Relation.ReflTransGen.refl
  | succ m ih =>
    intro hn
    have hm : m < k := by omega
    exact Relation.ReflTransGen.tail (ih hm) (sameObjectStep_succ c ⟨m, hm⟩ hn)

/-- **`SameObject` is total on every chain of this model.** The reason is the structure field `step_input`:
the elementary transitions are *given* as correct, so nothing can prevent all presentations from being
same-object. This is an honest limitation of the toy (see the module docstring): the quotient of §6 is a
subsingleton, and the burden of the invariance obligation therefore falls entirely on the constancy of the
reading — which is exactly what §8 tests. -/
theorem sameObject_total {k : ℕ} [NeZero k] (c : Chain k) : ∀ i j : Fin k, SameObject c i j := by
  intro i j
  exact Relation.ReflTransGen.trans
    (sameObject_symm c (sameObject_base_related c i.val i.isLt))
    (sameObject_base_related c j.val j.isLt)

/-- **The quotient is a subsingleton**, on any chain: one object with `k` presentations has a one-point
quotient. Consequence of `sameObject_total`. -/
theorem sameObject_quotient_subsingleton {k : ℕ} [NeZero k] (c : Chain k) :
    Subsingleton (Quotient (sameObjectSetoid c)) :=
  ⟨fun a b =>
    Quotient.ind (motive := fun a => ∀ b, a = b)
      (fun i =>
        Quotient.ind (motive := fun b => Quotient.mk (sameObjectSetoid c) i = b)
          (fun j => Quotient.sound (sameObject_total c i j)))
      a b⟩

/-! ## 6. The descent: the reading is a function on the quotient -/

/-- **One correct transition plus the cocycle law at the base frame preserve the reading.** If the transition
`i → j` transports the presentation (`input i * unit i j hij = input j`), then the two base-frame transports
coincide: both sides, multiplied by `unit (base) j`, give `input i * unit i j hij`. This is the per-step
content of the descent, and it is where the cocycle law is consumed for the *second* time. -/
theorem reading_eq_of_transport {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) {i j : Fin k}
    (hij : i.val ≤ j.val) (hstep : c.input i * c.unit i j hij = c.input j) :
    c.reading i = c.reading j := by
  have hmem : ‖c.unit (base k) j (base_le j) - 1‖ < 1 := c.unit_mem _ _ _
  have hne : c.unit (base k) j (base_le j) ≠ 0 := PadicLogVolume.ne_zero_of_norm_sub_one_lt hmem
  have hnei : c.unit (base k) i (base_le i) ≠ 0 :=
    PadicLogVolume.ne_zero_of_norm_sub_one_lt (c.unit_mem _ _ _)
  have hcoc := hc (base k) i j (base_le i) hij
  have hleft : c.relativeInput j * c.unit (base k) j (base_le j) = c.input i * c.unit i j hij := by
    rw [Chain.relativeInput, Chain.stepInv, mul_assoc, inv_mul_cancel₀ hne, mul_one, hstep]
  have hright : c.relativeInput i * c.unit (base k) j (base_le j) = c.input i * c.unit i j hij := by
    rw [Chain.relativeInput, Chain.stepInv, hcoc, mul_assoc, inv_mul_cancel_left₀ hnei]
  have hrel : c.relativeInput i = c.relativeInput j :=
    mul_right_cancel₀ hne (by rw [hright, hleft])
  rw [Chain.reading, Chain.reading, hrel]

/-- **Each one-step relation preserves the reading**, on a compatible chain: the two orientations of
`SameObjectStep` reduce to `reading_eq_of_transport`. -/
theorem sameObjectStep_reading {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) {i j : Fin k}
    (h : SameObjectStep c i j) : c.reading i = c.reading j := by
  rcases h with ⟨hij, hstep⟩ | ⟨hji, hstep⟩
  · exact reading_eq_of_transport c hc hij hstep
  · exact (reading_eq_of_transport c hc hji hstep).symm

/-- **The constancy obligation**: the reading is constant along `SameObject`, proved step by step from
`sameObjectStep_reading` — not by appealing to `reading_compatible` and ignoring the relation. This is the
hypothesis `Quotient.lift` asks for. -/
theorem sameObject_reading_eq {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) {i j : Fin k}
    (h : SameObject c i j) : c.reading i = c.reading j := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (sameObjectStep_reading c hc hbc)

/-- **The descended reading**: the reading, as a function on the quotient of presentations by "describing the
same object". The obligation is `sameObject_reading_eq`; this is the `Quotient.lift` of the task, and the
quotient is written `Quotient (sameObjectSetoid c)` because `SameObject c` is a relation and not itself a
`Setoid` (`sameObjectSetoid_rfl` records that the relation is unchanged by the packaging). -/
def descendedReading {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) :
    Quotient (sameObjectSetoid c) → ℚ_[3] :=
  Quotient.lift (fun i => c.reading i) (fun _ _ hab => sameObject_reading_eq c hc hab)

/-- **The descended function computes the original reading** — the computation rule of the lift. -/
theorem descendedReading_mk {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c) (i : Fin k) :
    descendedReading c hc (Quotient.mk (sameObjectSetoid c) i) = c.reading i :=
  Quotient.lift_mk (s := sameObjectSetoid c) (f := fun i => c.reading i)
    (fun _ _ hab => sameObject_reading_eq c hc hab) i

/-- **The descended reading is the base reading at every point of the quotient.** Since the quotient is a
subsingleton this could also be read off `sameObject_total`; it is proved here from `reading_eq_base`, so that
the value is visibly the logarithm of the base presentation and not an arbitrary number. -/
theorem descendedReading_const {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c)
    (q : Quotient (sameObjectSetoid c)) :
    descendedReading c hc q = CoreTransport.localLog (c.input (base k)) :=
  Quotient.ind
    (motive := fun q => descendedReading c hc q = CoreTransport.localLog (c.input (base k)))
    (fun i => by rw [descendedReading_mk, reading_eq_base c hc i]) q

/-- **The descent is unique**: any function on the quotient that computes the readings agrees with
`descendedReading`. This is the sense in which "descends to the quotient" is stronger than "constant on the
chain": it produces a *function on the classes*, and only one such function can compute the readings — a
statement with no chain-level analogue. -/
theorem descendedReading_unique {k : ℕ} [NeZero k] (c : Chain k) (hc : IsCompatible c)
    (f : Quotient (sameObjectSetoid c) → ℚ_[3])
    (hf : ∀ i : Fin k, f (Quotient.mk (sameObjectSetoid c) i) = c.reading i) :
    f = descendedReading c hc := by
  funext q
  exact Quotient.ind (motive := fun q => f q = descendedReading c hc q)
    (fun i => by rw [hf i, descendedReading_mk]) q

/-! ## 7. Two concrete three-presentation chains (W4's witnesses, restated)

Both chains have the same three presentations, `4, 16, 64 = 4^1, 4^2, 4^3`, and the same elementary
transitions (multiplication by `4`). They differ in exactly one comparison transition: from the base `0` to
`2`, the compatible chain records `4^2 = 16` and the other records `4^3 = 64`. -/

/-- The index `0` of a three-presentation chain. -/
def i0 : Fin 3 := ⟨0, by decide⟩

/-- The index `1`. -/
def i1 : Fin 3 := ⟨1, by decide⟩

/-- The index `2`. -/
def i2 : Fin 3 := ⟨2, by decide⟩

/-- The exponent of the transition unit in the compatible chain: `4 ^ (j - i)`. -/
def expCompat (i j : ℕ) : ℕ := j - i

/-- The exponent in the incompatible chain: `d + d / 2` with `d = j - i`, i.e. `d` for the elementary
transitions and `d + 1 = 3` for the comparison transition `0 → 2`. -/
def expBroken (i j : ℕ) : ℕ := j - i + (j - i) / 2

/-- `‖4 ^ n - 1‖ < 1` for every `n`: every power of `4` is a principal unit. -/
theorem norm_four_pow_sub_one (n : ℕ) : ‖(4 : ℚ_[3]) ^ n - 1‖ < 1 :=
  PadicLogVolume.norm_pow_sub_one_lt norm_four_sub_one n

/-- **A compatible chain**: presentations `4, 16, 64`, transitions acting by `4 ^ (j - i)`. The cocycle law
holds because `(j - i) + (l - j) = l - i` for `i ≤ j ≤ l`. -/
def chainCompat : Chain 3 where
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

/-- **The incompatible chain**: same presentations and same elementary transitions as `chainCompat`, but the
comparison transition `0 → 2` is recorded as `4 ^ 3 = 64` instead of `4 ^ 2 = 16`. -/
def chainBroken : Chain 3 where
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

/-- Non-vacuity at the type itself: `Chain 3` is inhabited by an actual chain. -/
example : Chain 3 := chainCompat

/-- **The compatible chain satisfies the cocycle law.** -/
theorem chainCompat_isCompatible : IsCompatible chainCompat := by
  intro i j l hij hjl
  show (4 : ℚ_[3]) ^ expCompat i.val l.val
      = (4 : ℚ_[3]) ^ expCompat i.val j.val * (4 : ℚ_[3]) ^ expCompat j.val l.val
  rw [expCompat, expCompat, expCompat, ← pow_add]
  congr 1
  omega

/-- The base presentation of the compatible chain is `4`. -/
theorem chainCompat_input_base : chainCompat.input (base 3) = (4 : ℚ_[3]) := by
  simp [chainCompat, base]

/-- **Every reading of the compatible chain is `localLog 4`.** -/
theorem chainCompat_reading (i : Fin 3) : chainCompat.reading i = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [reading_eq_base chainCompat chainCompat_isCompatible i, chainCompat_input_base]

/-- **The comparison transition `0 → 2` of the compatible chain transports the presentation**: `4 * 16 = 64`.
So `0` and `2` are related in one step there. -/
theorem chainCompat_transport_02 :
    chainCompat.input i0 * chainCompat.unit i0 i2 (by decide) = chainCompat.input i2 := by
  norm_num [chainCompat, i0, i2, expCompat]

/-- **The broken chain is not compatible.** At `(0,1,2)` the cocycle law would read `4 ^ 3 = 4 ^ 1 * 4 ^ 1`,
i.e. `64 = 16`, which is false; the failure is at a *comparison* transition, the elementary ones being
correct. -/
theorem chainBroken_not_compatible : ¬ IsCompatible chainBroken := by
  intro hc
  have h := hc i0 i1 i2 (by decide) (by decide)
  have h02 : chainBroken.unit i0 i2 (by decide) = (64 : ℚ_[3]) := by
    norm_num [chainBroken, i0, i2, expBroken]
  have h01 : chainBroken.unit i0 i1 (by decide) = (4 : ℚ_[3]) := by
    norm_num [chainBroken, i0, i1, expBroken]
  have h12 : chainBroken.unit i1 i2 (by decide) = (4 : ℚ_[3]) := by
    norm_num [chainBroken, i1, i2, expBroken]
  rw [h02, h01, h12] at h
  norm_num at h

/-! ## 8. Anti-degeneracy: on the incompatible chain the relation is smaller, yet must still relate
indices whose readings differ -/

/-- The elementary transport `0 → 1` of the broken chain: `4 * 4 = 16`. The elementary transitions are
untouched by the defect, so this is a genuine one-step relation. -/
theorem chainBroken_transport_01 :
    chainBroken.input i0 * chainBroken.unit i0 i1 (by decide) = chainBroken.input i1 := by
  norm_num [chainBroken, i0, i1, expBroken]

/-- The elementary transport `1 → 2` of the broken chain: `16 * 4 = 64`. -/
theorem chainBroken_transport_12 :
    chainBroken.input i1 * chainBroken.unit i1 i2 (by decide) = chainBroken.input i2 := by
  norm_num [chainBroken, i1, i2, expBroken]

/-- **The one-step relation is smaller on the broken chain**: the recorded comparison transition `0 → 2` is
`4^3 = 64`, so `4 * 64 = 256 ≠ 64`, and no one-step relation joins `0` to `2`. With explicit numbers. -/
theorem chainBroken_no_direct_edge :
    ¬ (∃ h : (i0).val ≤ (i2).val,
        chainBroken.input i0 * chainBroken.unit i0 i2 h = chainBroken.input i2) := by
  rintro ⟨h, he⟩
  have h4 : chainBroken.input i0 = (4 : ℚ_[3]) := by norm_num [chainBroken, i0]
  have hu : chainBroken.unit i0 i2 h = (64 : ℚ_[3]) := by
    norm_num [chainBroken, i0, i2, expBroken]
  have hi2 : chainBroken.input i2 = (64 : ℚ_[3]) := by norm_num [chainBroken, i2]
  rw [h4, hu, hi2] at he
  norm_num at he

/-- **`1` and `2` are related in one step on the broken chain** (`16 * 4 = 64`): the elementary transition is
correct there, so the relation cannot see the defect at `0 → 2`. -/
theorem chainBroken_sameObject_one_two : SameObject chainBroken i1 i2 :=
  Relation.ReflTransGen.single (Or.inl ⟨by decide, chainBroken_transport_12⟩)

/-- **`0` and `2` are related on the broken chain**, but only in *two* steps: `0 → 1 → 2`, through the
elementary transitions `4 * 4 = 16` and `16 * 4 = 64`. The closure restores the pair that the direct
transition lost — which is precisely why the defect has to be detected by the reading, not by the relation. -/
theorem chainBroken_sameObject : SameObject chainBroken i0 i2 :=
  Relation.ReflTransGen.head (Or.inl ⟨by decide, chainBroken_transport_01⟩)
    (Relation.ReflTransGen.single (Or.inl ⟨by decide, chainBroken_transport_12⟩))

/-- The transported presentation at `0` of the broken chain is `4`. -/
theorem chainBroken_relativeInput_zero : chainBroken.relativeInput i0 = 4 := by
  have hi : chainBroken.input i0 = (4 : ℚ_[3]) := by norm_num [chainBroken, i0]
  have hu : chainBroken.unit (base 3) i0 (base_le i0) = 1 := by
    norm_num [chainBroken, base, i0, expBroken]
  rw [Chain.relativeInput, Chain.stepInv, hi, hu]
  simp

/-- The transported presentation at `1` of the broken chain is `4`: `16 * 4⁻¹ = 4`, since the comparison
transition `0 → 1` is the correct `4`. -/
theorem chainBroken_relativeInput_one : chainBroken.relativeInput i1 = 4 := by
  have hi : chainBroken.input i1 = (16 : ℚ_[3]) := by norm_num [chainBroken, i1]
  have hu : chainBroken.unit (base 3) i1 (base_le i1) = (4 : ℚ_[3]) := by
    norm_num [chainBroken, base, i1, expBroken]
  rw [Chain.relativeInput, Chain.stepInv, hi, hu]
  have h16 : (16 : ℚ_[3]) = 4 * 4 := by norm_num
  rw [h16, mul_assoc, mul_inv_cancel₀ norm_four_ne_zero, mul_one]

/-- The transported presentation at `2` of the broken chain is `1`: the recorded transition `0 → 2` is `64`,
which cancels the input `64` there. -/
theorem chainBroken_relativeInput_two : chainBroken.relativeInput i2 = 1 := by
  have hi : chainBroken.input i2 = (4 : ℚ_[3]) ^ 3 := by norm_num [chainBroken, i2]
  have hu : chainBroken.unit (base 3) i2 (base_le i2) = (4 : ℚ_[3]) ^ 3 := by
    norm_num [chainBroken, base, i2, expBroken]
  rw [Chain.relativeInput, Chain.stepInv, hi, hu]
  exact mul_inv_cancel₀ (pow_ne_zero 3 norm_four_ne_zero)

/-- The reading at `0` of the broken chain is `localLog 4`. -/
theorem chainBroken_reading_zero : chainBroken.reading i0 = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [Chain.reading, chainBroken_relativeInput_zero]

/-- The reading at `1` of the broken chain is `localLog 4`. -/
theorem chainBroken_reading_one : chainBroken.reading i1 = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [Chain.reading, chainBroken_relativeInput_one]

/-- **The reading at `2` of the broken chain is `0`**, i.e. `localLog 1`. -/
theorem chainBroken_reading_two : chainBroken.reading i2 = 0 := by
  rw [Chain.reading, chainBroken_relativeInput_two, localLog_one]

/-- **Anti-degeneracy, first form: two indices related in one step whose readings differ.**
`1` and `2` are joined by the correct elementary transition (`16 * 4 = 64`), so they are same-object by
`chainBroken_sameObject_one_two`; their readings are `localLog 4` and `0`, separated by `localLog_four_ne_zero`.
This is a concrete witness chain with explicit numbers, not a negated universal. -/
theorem chainBroken_readings_one_two_differ : chainBroken.reading i1 ≠ chainBroken.reading i2 := by
  rw [chainBroken_reading_one, chainBroken_reading_two]
  exact localLog_four_ne_zero

/-- The same separation for the pair whose comparison transition is the defective one: readings `localLog 4`
at `0` and `0` at `2`. -/
theorem chainBroken_readings_differ : chainBroken.reading i0 ≠ chainBroken.reading i2 := by
  rw [chainBroken_reading_zero, chainBroken_reading_two]
  exact localLog_four_ne_zero

/-- **The lift's constancy hypothesis fails on the broken chain.** The hypothesis `Quotient.lift` needs is
`∀ i j, SameObject c i j → reading i = reading j`; it is refuted here by the related pair `1, 2` with
readings `localLog 4 ≠ 0`. -/
theorem constancy_not_universal_on_broken :
    ¬ (∀ i j : Fin 3, SameObject chainBroken i j →
        chainBroken.reading i = chainBroken.reading j) :=
  fun h => chainBroken_readings_one_two_differ (h i1 i2 chainBroken_sameObject_one_two)

/-- **Therefore no function on the quotient computes the readings of the broken chain**: there is no
`f : Quotient (sameObjectSetoid chainBroken) → ℚ_[3]` with `f ⟦i⟧ = reading i` for all `i`. Had such an `f`
existed, the related pair `1, 2` would have equal readings. This is the sharpest form of item 6's second
alternative, and it is stated about the quotient itself, not merely about the relation. -/
theorem no_factorization_on_broken :
    ¬ ∃ f : Quotient (sameObjectSetoid chainBroken) → ℚ_[3],
        ∀ i : Fin 3, f (Quotient.mk (sameObjectSetoid chainBroken) i) = chainBroken.reading i := by
  rintro ⟨f, hf⟩
  apply chainBroken_readings_one_two_differ
  rw [← hf i1, ← hf i2, Quotient.sound chainBroken_sameObject_one_two]

/-- **The descended reading of the compatible chain is `localLog 4` everywhere on the quotient.** -/
theorem descendedReading_chainCompat_const (q : Quotient (sameObjectSetoid chainCompat)) :
    descendedReading chainCompat chainCompat_isCompatible q
      = CoreTransport.localLog (4 : ℚ_[3]) := by
  rw [descendedReading_const chainCompat chainCompat_isCompatible q, chainCompat_input_base]

/-- **The two chains side by side, with explicit numbers.** The compatible chain relates `0` and `2` in one
step (`4 * 16 = 64`), the broken chain does not (`4 * 64 = 256 ≠ 64`) but still relates them in two steps,
and its readings at the related pair `1, 2` differ (`localLog 4` against `0`). So on the same presentations
the descent exists for one chain and provably does not for the other. -/
theorem one_step_versus_two_steps :
    chainCompat.input i0 * chainCompat.unit i0 i2 (by decide) = chainCompat.input i2 ∧
      SameObject chainBroken i0 i2 ∧
      chainBroken.reading i1 = CoreTransport.localLog (4 : ℚ_[3]) ∧
      chainBroken.reading i2 = 0 ∧
      chainBroken.reading i1 ≠ chainBroken.reading i2 :=
  ⟨chainCompat_transport_02, chainBroken_sameObject, chainBroken_reading_one,
    chainBroken_reading_two, chainBroken_readings_one_two_differ⟩

/-- **The anti-degeneracy statement, existentially stated**: there is a chain whose transitions fail the
cocycle law, whose `SameObject` relates the indices `1` and `2`, and whose readings there differ. -/
theorem exists_incompatible_chain_with_related_unequal_readings :
    ∃ c : Chain 3, ¬ IsCompatible c ∧ SameObject c i1 i2 ∧ c.reading i1 ≠ c.reading i2 :=
  ⟨chainBroken, chainBroken_not_compatible, chainBroken_sameObject_one_two,
    chainBroken_readings_one_two_differ⟩

end

end ReadingFactorization

#print axioms ReadingFactorization.algorithmRun
#print axioms ReadingFactorization.algorithmRun_eq_partialSums
#print axioms ReadingFactorization.localLog_eq_padicLog
#print axioms ReadingFactorization.hasSum_logTerm_localLog
#print axioms ReadingFactorization.base
#print axioms ReadingFactorization.base_le
#print axioms ReadingFactorization.Chain
#print axioms ReadingFactorization.Chain.stepInv
#print axioms ReadingFactorization.Chain.relativeInput
#print axioms ReadingFactorization.Chain.reading
#print axioms ReadingFactorization.IsCompatible
#print axioms ReadingFactorization.norm_four_sub_one
#print axioms ReadingFactorization.Chain.relativeInput_mem
#print axioms ReadingFactorization.Chain.reading_hasSum
#print axioms ReadingFactorization.Chain.reading_is_limit_of_algorithm
#print axioms ReadingFactorization.Chain.stepInv_step
#print axioms ReadingFactorization.input_transport_aux
#print axioms ReadingFactorization.input_transport
#print axioms ReadingFactorization.reading_eq_base
#print axioms ReadingFactorization.reading_compatible
#print axioms ReadingFactorization.norm_two_Q3
#print axioms ReadingFactorization.norm_two_mul_three
#print axioms ReadingFactorization.norm_three_le_two_mul_three
#print axioms ReadingFactorization.norm_logRem_three_le
#print axioms ReadingFactorization.localLog_one
#print axioms ReadingFactorization.localLog_four
#print axioms ReadingFactorization.localLog_four_ne_zero
#print axioms ReadingFactorization.norm_four_ne_zero
#print axioms ReadingFactorization.SameObjectStep
#print axioms ReadingFactorization.SameObject
#print axioms ReadingFactorization.sameObjectStep_symm
#print axioms ReadingFactorization.reflTransGen_symm
#print axioms ReadingFactorization.sameObject_refl
#print axioms ReadingFactorization.sameObjectStep_refl
#print axioms ReadingFactorization.sameObject_trans
#print axioms ReadingFactorization.sameObject_symm
#print axioms ReadingFactorization.sameObject_equivalence
#print axioms ReadingFactorization.sameObjectSetoid
#print axioms ReadingFactorization.sameObjectSetoid_rfl
#print axioms ReadingFactorization.sameObjectStep_succ
#print axioms ReadingFactorization.sameObjectStep_of_compatible
#print axioms ReadingFactorization.sameObjectStep_direct
#print axioms ReadingFactorization.sameObject_base_related
#print axioms ReadingFactorization.sameObject_total
#print axioms ReadingFactorization.sameObject_quotient_subsingleton
#print axioms ReadingFactorization.reading_eq_of_transport
#print axioms ReadingFactorization.sameObjectStep_reading
#print axioms ReadingFactorization.sameObject_reading_eq
#print axioms ReadingFactorization.descendedReading
#print axioms ReadingFactorization.descendedReading_mk
#print axioms ReadingFactorization.descendedReading_const
#print axioms ReadingFactorization.descendedReading_unique
#print axioms ReadingFactorization.i0
#print axioms ReadingFactorization.i1
#print axioms ReadingFactorization.i2
#print axioms ReadingFactorization.expCompat
#print axioms ReadingFactorization.expBroken
#print axioms ReadingFactorization.norm_four_pow_sub_one
#print axioms ReadingFactorization.chainCompat
#print axioms ReadingFactorization.chainBroken
#print axioms ReadingFactorization.chainCompat_isCompatible
#print axioms ReadingFactorization.chainCompat_input_base
#print axioms ReadingFactorization.chainCompat_reading
#print axioms ReadingFactorization.chainCompat_transport_02
#print axioms ReadingFactorization.chainBroken_transport_01
#print axioms ReadingFactorization.chainBroken_transport_12
#print axioms ReadingFactorization.chainBroken_no_direct_edge
#print axioms ReadingFactorization.chainBroken_sameObject_one_two
#print axioms ReadingFactorization.chainBroken_sameObject
#print axioms ReadingFactorization.chainBroken_relativeInput_zero
#print axioms ReadingFactorization.chainBroken_relativeInput_one
#print axioms ReadingFactorization.chainBroken_relativeInput_two
#print axioms ReadingFactorization.chainBroken_reading_zero
#print axioms ReadingFactorization.chainBroken_reading_one
#print axioms ReadingFactorization.chainBroken_reading_two
#print axioms ReadingFactorization.chainBroken_readings_one_two_differ
#print axioms ReadingFactorization.chainBroken_readings_differ
#print axioms ReadingFactorization.constancy_not_universal_on_broken
#print axioms ReadingFactorization.no_factorization_on_broken
#print axioms ReadingFactorization.descendedReading_chainCompat_const
#print axioms ReadingFactorization.one_step_versus_two_steps
#print axioms ReadingFactorization.exists_incompatible_chain_with_related_unequal_readings
#print axioms ReadingFactorization.chainBroken_not_compatible
