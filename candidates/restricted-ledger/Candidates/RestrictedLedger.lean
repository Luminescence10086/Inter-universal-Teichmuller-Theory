import IUTBridge.WeightedLedger
import IUTBridge.Integration

/-!
# A finite integer certificate for ledger preservation on a restricted domain

This is a **candidate** development. It is not admitted to any fact-tree, it changes
no receipt, and it names no IUT/abc claim. It reuses the already admitted ledger of
`IUTBridge.WeightedLedger` and `IUTBridge.Integration` verbatim; nothing here
redefines the ledger under a new name.

## The question

`IUTBridge.Integration.weightedLedger_combined_invariant_iff` decides preservation of
the weighted ledger `L_w x = Σ_j w_j · v(x_j)` on the **whole** coordinatewise
nonzero locus, and its proof uses two probes there: the constant-one tuple and the
`deltaTuple` family. A real admissible domain `Ω` need not contain those probes, so
the global criterion says nothing about preservation *on `Ω`*.

Fix a domain `Ω` of tuples with coordinatewise nonzero entries, a weight vector
`w : Fin n → ℤ`, a label permutation `σ`, a scalar family `a` with every `a j ≠ 0`,
and a base point `x₀ ∈ Ω`. Put

```
f e  = Σ_j (w (σ j) - w j) * e j        (integer functional)
c    = Σ_j w (σ j) * (a j).valuation     (scalar budget)
e₀   = vprofile x₀
```

Given finitely many integer generators `b : Fin r → (Fin n → ℤ)` such that

* `hgen : ∀ x ∈ Ω, ∃ lam, vprofile x - e₀ = Σ_i lam i • b i`  (the generators span
  all profile differences over `ℤ`), and
* `hreal : ∀ i, ∃ x ∈ Ω, vprofile x - e₀ = b i`  (each generator is *realised* by
  an actual point of `Ω`),

the main result `restricted_ledger_criterion` is the exact equivalence

```
(∀ x ∈ Ω, L_w (relabel σ (slotwise a x)) = L_w x)  ↔  f e₀ + c = 0 ∧ ∀ i, f (b i) = 0.
```

This original result is retained with its stronger realisation premise. The results
at the end of this file replace that premise by arbitrary finite integer combinations
of actual differences in both directions; see `integer_combination_criterion` and
`restricted_ledger_combination_criterion`. The general span-certificate version is
`restricted_ledger_span_criterion`, whose premise `hspan : ∀ i, MemDiffSpanOn Ω x₀
(b i)` says only that each generator lies in the `ℤ`-span of the actual profile
differences realised inside `Ω`. `restricted_ledger_criterion_of_combination` derives
the strong-premise version from it, so the two versions are related by an explicit
inclusion rather than being independent assumptions. The converse inclusion fails and
is refuted by `finite_integer_span_membership_example`.

## Hypotheses, nonemptiness, and the empty domain

* Nonemptiness is carried explicitly by `x₀ ∈ Ω`. It cannot be dropped: the
  preservation statement is vacuous on `Ω = ∅`, while the certificate needs a base
  point. `empty_domain_vacuous` exhibits this gap concretely (an empty domain whose
  preservation statement holds while the corresponding integer equation fails).
* The coordinatewise nonzero hypothesis `hΩ : ∀ x ∈ Ω, ∀ j, x j ≠ 0` is explicit,
  not hidden in a structure field: p-adic valuations are only additive on nonzero
  elements, so `vprofile` is only meaningful for the ledger on that locus.
* The nonzero scalars `ha : ∀ j, a j ≠ 0` are likewise explicit. `hgen` and `hreal`
  are independent structural hypotheses about the domain; neither mentions `w`,
  `a` or the ledger, so the ledger equation is never assumed.

## Two independent obligations

Preservation **on** `Ω` (what this file decides) and invariance of `Ω` under the
transformation `T = relabel σ ∘ slotwise a` (that is, `T Ω ⊆ Ω`) are separate
obligations. `domain_not_preserved_by_slotwise` exhibits a scalar action that keeps
the ledger criterion intact while moving the exhibited domain out of itself. This
file says nothing about `T Ω ⊆ Ω` in general.

## The two required instances

* `equal_valuation_two_slot_example`: on the two-slot domain of *equal* valuations,
  the swap `0 ↔ 1` with weights `(1, 2)` and scalars all `1` **does** preserve the
  weighted ledger, even though `w` is not permutation invariant. This is the point:
  preservation on a restricted domain does not require global invariance of `w`.
* `full_domain_specialization`: with `Ω` the coordinatewise nonzero locus and the
  `deltaTuple`-style unit generators, the restricted criterion's *necessary*
  direction gives `∀ j, w (σ j) = w j` only. It does not give the scalar budget and
  it is not the full `weightedLedger_combined_invariant_iff`.
* `full_domain_iff`: the corresponding full equivalence on the same locus,
  `(preservation) ↔ (∀ j, w (σ j) = w j) ∧ (Σ_j w (σ j) v(a_j) = 0)`, derived
  through the general span certificate.

## What the full-space specialisation does and does not give

The second conjunct above is stated with the *relabelled* weights `w (σ j)`; the
admitted `weightedLedger_combined_invariant_iff` states its budget with `w j`. Under
the first conjunct the two budgets agree, so the two statements have the same content
— but this file derives its version through the restricted route and therefore
`instantiates` the admitted theorem, it does not reprove, replace or strengthen it.
Neither `full_domain_specialization` nor `full_domain_iff` is claimed to *restore the
whole old criterion*: they are specialisations of the finite certificate to
`Ω = {x | ∀ j, x j ≠ 0}`, sharing its hypotheses (a base point, coordinatewise
nonzero points, nonzero scalars) verbatim. The added information is only *why* the
global probes are the delta tuples: they realise the unit generators. Restoration of
the admitted global criterion in its own form is not claimed.

Scope. Slots are an abstract `Fin n`, weights are arbitrary integers, tuples are
actual `ℚ_[p]`. No Ism/Kummer element, packet, seed region, Arakelov volume or
Step (v) claim is constructed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Candidates.RestrictedLedger

noncomputable section

open Classical IUTBridge.Slots IUTBridge.WeightedLedger

variable (p : Nat) [hp : Fact p.Prime]

/-! ## Integer vectors: the dot-product functional -/

/-- The integer dot product of a weight functional `d` with an integer vector `e`.
This is the finite, purely integer object the p-adic ledger reduces to. -/
def dot {n : Nat} (d e : Fin n → ℤ) : ℤ := ∑ j, d j * e j

/-- The dot product is additive in the vector. -/
theorem dot_add {n : Nat} (d e₁ e₂ : Fin n → ℤ) :
    dot d (e₁ + e₂) = dot d e₁ + dot d e₂ := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The dot product is additive in the vector, subtractively. -/
theorem dot_sub {n : Nat} (d e₁ e₂ : Fin n → ℤ) :
    dot d (e₁ - e₂) = dot d e₁ - dot d e₂ := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The dot product is homogeneous for integer scalars. -/
theorem dot_smul {n : Nat} (d e : Fin n → ℤ) (k : ℤ) :
    dot d (k • e) = k * dot d e := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The dot product of a finite integer combination of generators. -/
theorem dot_sum {n r : Nat} (d : Fin n → ℤ) (lam : Fin r → ℤ)
    (b : Fin r → Fin n → ℤ) :
    dot d (∑ i, lam i • b i) = ∑ i, lam i * dot d (b i) := by
  have hpt : ∀ j : Fin n, (∑ i, lam i • b i : Fin n → ℤ) j = ∑ i, lam i * b i j := by
    intro j
    simp [Finset.sum_apply]
  simp only [dot, hpt, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The dot product against a unit integer vector is the corresponding weight. -/
theorem dot_single {n : Nat} (d : Fin n → ℤ) (i : Fin n) :
    dot d (fun j => if j = i then (1 : ℤ) else 0) = d i := by
  simp only [dot]
  have hzero : ∀ j ∈ Finset.univ, j ≠ i →
      d j * (if j = i then (1 : ℤ) else 0) = 0 := by
    intro j _ hj
    simp [hj]
  rw [Finset.sum_eq_single i hzero (by
    intro hi
    exact absurd (Finset.mem_univ i) hi)]
  simp

/-- **The finite integer span criterion.** Let `S` be a set of integer vectors
containing `e₀`, all of whose elements differ from `e₀` by an integer combination of
the generators `b i`, and suppose moreover that every generator `b i` is *realised*
as `e - e₀` for some `e ∈ S`. Then the affine integer functional `e ↦ d · e + c`
vanishes on all of `S` iff it vanishes at `e₀` and at every generator. -/
theorem integer_span_criterion {n r : Nat} (d e₀ : Fin n → ℤ) (c : ℤ)
    (b : Fin r → Fin n → ℤ) (S : Set (Fin n → ℤ))
    (he₀ : e₀ ∈ S)
    (hgen : ∀ e ∈ S, ∃ lam : Fin r → ℤ, e - e₀ = ∑ i, lam i • b i)
    (hreal : ∀ i, ∃ e ∈ S, e - e₀ = b i) :
    (∀ e ∈ S, dot d e + c = 0) ↔ (dot d e₀ + c = 0 ∧ ∀ i, dot d (b i) = 0) := by
  constructor
  · intro h
    refine ⟨h e₀ he₀, fun i => ?_⟩
    obtain ⟨e, heS, hee⟩ := hreal i
    have h₁ : dot d e + c = 0 := h e heS
    have h₀ : dot d e₀ + c = 0 := h e₀ he₀
    have hsub : dot d (b i) = dot d (e - e₀) := by rw [hee]
    rw [hsub, dot_sub]
    omega
  · rintro ⟨h₀, hb⟩ e heS
    obtain ⟨lam, hlam⟩ := hgen e heS
    have heq : e = e₀ + ∑ i, lam i • b i := by
      rw [← hlam]
      funext j
      simp only [Pi.add_apply, Pi.sub_apply]
      omega
    rw [heq, dot_add, dot_sum]
    simp only [hb, mul_zero, Finset.sum_const_zero, add_zero]
    exact h₀

/-! ## The exact p-adic ledger shift -/

/-- **The exact ledger shift formula.** For a coordinatewise nonzero tuple and a
scalar family with every entry nonzero, the change of the weighted ledger under
`relabel σ ∘ slotwise a` is the integer functional `f` evaluated at the valuation
profile of `x`, plus the scalar budget `c`. Both existing lemmas
(`weightedLedger_relabel`, `weightedLedger_slotwise`) are used only as they stand. -/
theorem weightedLedger_shift {n : Nat} (σ : Equiv.Perm (Fin n)) (w : Fin n → ℤ)
    (a : Fin n → ℚ_[p]) (x : Tuple p n) (ha : ∀ j, a j ≠ 0) (hx : ∀ j, x j ≠ 0) :
    weightedLedger p w (relabel p σ (slotwise p a x)) - weightedLedger p w x =
      dot (fun j => w (σ j) - w j) (vprofile p x)
        + ∑ j, w (σ j) * (a j).valuation := by
  have hmain := IUTBridge.Integration.weightedLedger_relabel_slotwise p σ w a x ha hx
  have hd : weightedLedger p (fun j => w (σ j)) x - weightedLedger p w x =
      dot (fun j => w (σ j) - w j) (vprofile p x) := by
    simp only [dot, weightedLedger]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (sub_mul _ _ _).symm
  calc weightedLedger p w (relabel p σ (slotwise p a x)) - weightedLedger p w x
      = (weightedLedger p (fun j => w (σ j)) x - weightedLedger p w x)
          + ∑ j, w (σ j) * (a j).valuation := by
        rw [hmain, add_sub_right_comm]
    _ = dot (fun j => w (σ j) - w j) (vprofile p x)
          + ∑ j, w (σ j) * (a j).valuation := by
        rw [hd]

/-! ## The main criterion on a restricted domain -/

/-- **The finite integer certificate.** On a domain `Ω` of coordinatewise nonzero
tuples, containing the explicit base point `x₀`, preservation of the weighted ledger
under `relabel σ ∘ slotwise a` is equivalent to the finite list of integer equations
`f e₀ + c = 0` and `f (b i) = 0` for every generator.

The hypotheses are exactly those stated in the module docstring: `hΩ` (coordinatewise
nonzero on `Ω`), `ha` (nonzero scalars), `hx₀` (nonemptiness of `Ω`), `hgen`
(finite integer spanning of the profile differences) and `hreal` (each generator is
realised inside `Ω`). No hypothesis mentions the ledger equation. -/
theorem restricted_ledger_criterion {n r : Nat} (Ω : Set (Tuple p n))
    (hΩ : ∀ x ∈ Ω, ∀ j, x j ≠ 0)
    (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0)
    (x₀ : Tuple p n) (hx₀ : x₀ ∈ Ω) (b : Fin r → Fin n → ℤ)
    (hgen : ∀ x ∈ Ω, ∃ lam : Fin r → ℤ, vprofile p x - vprofile p x₀ = ∑ i, lam i • b i)
    (hreal : ∀ i, ∃ x ∈ Ω, vprofile p x - vprofile p x₀ = b i) :
    (∀ x ∈ Ω, weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
      dot (fun j => w (σ j) - w j) (vprofile p x₀)
          + ∑ j, w (σ j) * (a j).valuation = 0
        ∧ ∀ i, dot (fun j => w (σ j) - w j) (b i) = 0 := by
  have hpoint : ∀ x ∈ Ω,
      (weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
        dot (fun j => w (σ j) - w j) (vprofile p x)
          + ∑ j, w (σ j) * (a j).valuation = 0 := by
    intro x hx
    rw [← sub_eq_zero, weightedLedger_shift p σ w a x ha (hΩ x hx)]
  have himg : (∀ e ∈ vprofile p '' Ω,
        dot (fun j => w (σ j) - w j) e + ∑ j, w (σ j) * (a j).valuation = 0) ↔
      ∀ x ∈ Ω, dot (fun j => w (σ j) - w j) (vprofile p x)
        + ∑ j, w (σ j) * (a j).valuation = 0 := by
    constructor
    · intro h x hx
      exact h _ ⟨x, hx, rfl⟩
    · rintro h _ ⟨x, hx, rfl⟩
      exact h x hx
  rw [forall₂_congr hpoint, ← himg]
  exact integer_span_criterion (fun j => w (σ j) - w j) (vprofile p x₀)
    (∑ j, w (σ j) * (a j).valuation) b (vprofile p '' Ω)
    ⟨x₀, hx₀, rfl⟩
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := he
      exact hgen x hx)
    (fun i => by
      obtain ⟨x, hx, hpx⟩ := hreal i
      exact ⟨vprofile p x, ⟨x, hx, rfl⟩, hpx⟩)

/-! ## Instance 1: the equal-valuation two-slot domain -/

/-- The non-uniform weight vector `(1, 2)` on two slots. It is deliberately **not**
invariant under the slot swap. -/
def swapWeights : Fin 2 → ℤ := fun j => if j = 0 then 1 else 2

/-- The restricted admissible domain: both coordinates nonzero and of **equal**
p-adic valuation. -/
def equalValuationDomain : Set (Tuple p 2) :=
  {x | x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ (x 0).valuation = (x 1).valuation}

/-- The domain is nonempty; the all-ones tuple is an explicit member. -/
theorem equalValuationDomain_nonempty :
    (fun _ : Fin 2 => (1 : ℚ_[p])) ∈ equalValuationDomain p := by
  refine ⟨one_ne_zero, one_ne_zero, ?_⟩
  rw [Padic.valuation_one]

/-- On the equal-valuation domain the valuation profile is constant. -/
theorem vprofile_of_equal_valuation {x : Tuple p 2} (hx : x ∈ equalValuationDomain p) :
    vprofile p x = fun _ => (x 0).valuation := by
  funext j
  fin_cases j
  · rfl
  · exact hx.2.2.symm

/-- The valuation profile of the all-ones tuple is identically zero. -/
theorem vprofile_one_tuple {n : Nat} :
    vprofile p (fun _ : Fin n => (1 : ℚ_[p])) = fun _ => (0 : ℤ) := by
  funext j
  exact Padic.valuation_one

/-- The valuation profile of the constant tuple `p` is identically one. -/
theorem vprofile_pTuple {n : Nat} :
    vprofile p (fun _ : Fin n => (p : ℚ_[p])) = fun _ => (1 : ℤ) := by
  funext j
  exact Padic.valuation_p

/-- The single generator `(1,1)` spans every profile difference inside the
equal-valuation domain. -/
theorem equalValuationDomain_span {x : Tuple p 2} (hx : x ∈ equalValuationDomain p) :
    ∃ lam : Fin 1 → ℤ,
      vprofile p x - vprofile p (fun _ : Fin 2 => (1 : ℚ_[p])) =
        ∑ i, lam i • (fun _ : Fin 2 => (1 : ℤ)) := by
  refine ⟨fun _ => (x 0).valuation, ?_⟩
  rw [vprofile_of_equal_valuation p hx, vprofile_one_tuple p]
  funext j
  simp [Pi.sub_apply]

/-- The generator `(1,1)` is realised inside the domain, by the tuple `(p,p)`. -/
theorem equalValuationDomain_realises_generator :
    ∃ x ∈ equalValuationDomain p,
      vprofile p x - vprofile p (fun _ : Fin 2 => (1 : ℚ_[p])) =
        (fun _ : Fin 2 => (1 : ℤ)) := by
  refine ⟨fun _ : Fin 2 => (p : ℚ_[p]), ?_, ?_⟩
  · refine ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero, Nat.cast_ne_zero.mpr hp.out.ne_zero, ?_⟩
    rw [Padic.valuation_p]
  · rw [vprofile_pTuple p, vprofile_one_tuple p]
    funext j
    simp [Pi.sub_apply]

/-- The two weights are **not** invariant under the swap `0 ↔ 1`. -/
theorem swapWeights_not_invariant :
    ¬ ∀ j : Fin 2, swapWeights (Equiv.swap 0 1 j) = swapWeights j := by
  decide

/-- **Instance 1: a restricted admissible domain preserves the ledger although the
weights are not permutation invariant.**

Here `n = 2`, `σ` is the swap `0 ↔ 1`, `w = (1,2)`, all scalars are `1`, and
`Ω = equalValuationDomain` is the locus of coordinatewise nonzero tuples whose two
valuations agree. The ledger is preserved on `Ω` — the swap exchanges the two
weights but the two valuations are equal, so the weighted total is unchanged — while
`w (σ 0) ≠ w 0`. Preservation on a domain therefore does **not** require global
permutation invariance of the weight vector. -/
theorem equal_valuation_two_slot_example :
    (∀ x ∈ equalValuationDomain p,
        weightedLedger p swapWeights
            (relabel p (Equiv.swap 0 1) (slotwise p (fun _ => (1 : ℚ_[p])) x)) =
          weightedLedger p swapWeights x) ∧
      ¬ ∀ j : Fin 2, swapWeights (Equiv.swap 0 1 j) = swapWeights j := by
  refine ⟨?_, swapWeights_not_invariant⟩
  refine (restricted_ledger_criterion p (equalValuationDomain p) ?_ swapWeights
    (Equiv.swap 0 1) (fun _ => (1 : ℚ_[p])) (fun _ => one_ne_zero)
    (fun _ : Fin 2 => (1 : ℚ_[p])) (equalValuationDomain_nonempty p)
    (fun _ : Fin 1 => fun _ : Fin 2 => (1 : ℤ))
    (fun x hx => equalValuationDomain_span p hx)
    (fun i => by
      obtain ⟨x, hx, hpx⟩ := equalValuationDomain_realises_generator p
      exact ⟨x, hx, hpx⟩)).mpr ⟨?_, ?_⟩
  · intro x hx j
    fin_cases j
    · exact hx.1
    · exact hx.2.1
  · -- the base-point equation `f e₀ + c = 0`
    simp [dot, vprofile, swapWeights]
  · -- the generator equation `f (1,1) = 0`
    intro i
    fin_cases i
    have h0 : Equiv.swap (0 : Fin 2) 1 0 = 1 := by decide
    have h1 : Equiv.swap (0 : Fin 2) 1 1 = 0 := by decide
    simp [dot, swapWeights, Fin.sum_univ_two, h0, h1]

/-- **`T Ω ⊆ Ω` is a genuinely separate obligation.** With the scalar family
`(p, 1)` the same restricted domain is *not* preserved by the slotwise action: the
all-ones tuple lands outside `Ω` because only one valuation is shifted. Nothing in
the ledger criterion asserts invariance of `Ω`. -/
theorem domain_not_preserved_by_slotwise :
    ∃ a : Fin 2 → ℚ_[p], (∀ j, a j ≠ 0) ∧
      ¬ ∀ x ∈ equalValuationDomain p, slotwise p a x ∈ equalValuationDomain p := by
  refine ⟨fun j => if j = 0 then (p : ℚ_[p]) else 1, ?_, ?_⟩
  · intro j
    fin_cases j
    · simp [hp.out.ne_zero]
    · simp
  · intro h
    have hones : (fun _ : Fin 2 => (1 : ℚ_[p])) ∈ equalValuationDomain p :=
      equalValuationDomain_nonempty p
    have himg := h _ hones
    have hval : ((p : ℚ_[p])).valuation = ((1 : ℚ_[p])).valuation := by
      simpa [slotwise] using himg.2.2
    rw [Padic.valuation_p, Padic.valuation_one] at hval
    exact absurd hval (by norm_num)

/-! ## Instance 2: recovering the global criterion on the full nonzero domain -/

/-- The coordinatewise nonzero domain, i.e. the domain of the existing global
criterion `weightedLedger_combined_invariant_iff`. -/
def nonzeroDomain (n : Nat) : Set (Tuple p n) := {x | ∀ j, x j ≠ 0}

/-- The all-ones tuple belongs to the full nonzero domain. -/
theorem nonzeroDomain_one_mem {n : Nat} :
    (fun _ : Fin n => (1 : ℚ_[p])) ∈ nonzeroDomain p n := fun _ => one_ne_zero

/-- Every profile difference on the full nonzero domain is an integer combination of
the `deltaTuple`-style unit vectors. -/
theorem nonzeroDomain_span {n : Nat} {x : Tuple p n} (_hx : ∀ j, x j ≠ 0) :
    ∃ lam : Fin n → ℤ,
      vprofile p x - vprofile p (fun _ : Fin n => (1 : ℚ_[p])) =
        ∑ i, lam i • (fun j => if j = i then (1 : ℤ) else 0) := by
  refine ⟨fun i => vprofile p x i, ?_⟩
  rw [vprofile_one_tuple p]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hzero : ∀ i ∈ Finset.univ, i ≠ j →
      vprofile p x i * (if j = i then (1 : ℤ) else 0) = 0 := by
    intro i _ hij
    have hji : j ≠ i := fun h => hij h.symm
    simp [hji]
  rw [Finset.sum_eq_single j hzero (by
    intro hj
    exact absurd (Finset.mem_univ j) hj)]
  simp

/-- Each unit generator is realised on the full nonzero domain by the actual
`deltaTuple`, which has no zero coordinate. -/
theorem nonzeroDomain_realises_generator {n : Nat} (i : Fin n) :
    ∃ x ∈ nonzeroDomain p n,
      vprofile p x - vprofile p (fun _ : Fin n => (1 : ℚ_[p])) =
        (fun j => if j = i then (1 : ℤ) else 0) := by
  refine ⟨deltaTuple p i, IUTBridge.Integration.deltaTuple_ne_zero p i, ?_⟩
  rw [vprofile_delta p i, vprofile_one_tuple p]
  funext j
  simp [Pi.sub_apply]

/-- **Instance 2: the global criterion as a special case of the restricted one.**

Take `Ω` to be the whole coordinatewise nonzero locus, `x₀` the all-ones tuple
(whose profile is `0`), and the `n` generators `b i = (δ_{i j})_j` — the valuation
profiles of `IUTBridge.WeightedLedger.deltaTuple`, realised inside `Ω` by
`deltaTuple_ne_zero`. The restricted criterion then produces
`∀ i, f (b i) = 0`, i.e. `w (σ i) = w i` for every slot: exactly the conclusion of
`IUTBridge.WeightedLedger.weightedLedger_invariant_iff`.

This **instantiates** the already admitted theorem; it does not replace it and it is
not independent of it. The content added here is only the restricted-domain route
(through `restricted_ledger_criterion`), which explains *why* the global criterion's
probes are the delta tuples: they are the realising witnesses of the unit generators. -/
theorem full_domain_specialization {n : Nat} (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0)
    (hpres : ∀ x : Tuple p n, (∀ j, x j ≠ 0) →
      weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) :
    ∀ j, w (σ j) = w j := by
  have hcert := (restricted_ledger_criterion p (nonzeroDomain p n)
    (fun _ hx => hx) w σ a ha (fun _ : Fin n => (1 : ℚ_[p])) (nonzeroDomain_one_mem p)
    (fun i => fun j => if j = i then (1 : ℤ) else 0)
    (fun x hx => nonzeroDomain_span p hx)
    (fun i => nonzeroDomain_realises_generator p i)).mp hpres
  intro j
  have hb := hcert.2 j
  rw [dot_single] at hb
  exact sub_eq_zero.mp hb

/-! ## The empty domain: why nonemptiness cannot be dropped -/

/-- The weighted scalar budget of the exhibited instance is `3`, not `0`. -/
theorem swapWeights_budget :
    (∑ j : Fin 2, swapWeights (Equiv.swap 0 1 j) * (1 : ℤ)) = 3 := by
  have h0 : Equiv.swap (0 : Fin 2) 1 0 = 1 := by decide
  have h1 : Equiv.swap (0 : Fin 2) 1 1 = 0 := by decide
  rw [Fin.sum_univ_two]
  norm_num [swapWeights, h0, h1]

/-- **The empty domain carries no information.** On `Ω = ∅` the preservation
statement holds vacuously, while the integer equation `f e₀ + c = 0` of the exhibited
configuration fails (`c = 3`). So the preservation statement alone yields *no*
necessary condition on the weights. The base-point premise cannot be dropped.
The stronger `hreal` premise of the original criterion is replaced by general
integer-combination membership in the repair criterion below. -/
theorem empty_domain_vacuous :
    (∀ x ∈ (∅ : Set (Tuple p 2)),
        weightedLedger p swapWeights
            (relabel p (Equiv.swap 0 1) (slotwise p (fun _ => (p : ℚ_[p])) x)) =
          weightedLedger p swapWeights x) ∧
      ¬ (dot (fun j : Fin 2 => swapWeights (Equiv.swap 0 1 j) - swapWeights j)
            (fun _ : Fin 2 => (0 : ℤ))
          + ∑ j : Fin 2, swapWeights (Equiv.swap 0 1 j) *
              ((fun _ : Fin 2 => (p : ℚ_[p])) j).valuation = 0) := by
  refine ⟨fun x hx => absurd hx (Set.notMem_empty x), ?_⟩
  have hz : (∑ j : Fin 2, swapWeights (Equiv.swap 0 1 j) *
      ((fun _ : Fin 2 => (p : ℚ_[p])) j).valuation) = 3 := by
    have hcongr : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
        swapWeights (Equiv.swap 0 1 j) * ((fun _ : Fin 2 => (p : ℚ_[p])) j).valuation =
          swapWeights (Equiv.swap 0 1 j) * (1 : ℤ) := by
      intro j _
      rw [show ((fun _ : Fin 2 => (p : ℚ_[p])) j).valuation = (1 : ℤ) from Padic.valuation_p]
    rw [Finset.sum_congr rfl hcongr]
    exact swapWeights_budget
  have hdot : dot (fun j : Fin 2 => swapWeights (Equiv.swap 0 1 j) - swapWeights j)
      (fun _ : Fin 2 => (0 : ℤ)) = 0 := by
    simp [dot]
  intro h
  rw [hdot, hz] at h
  norm_num at h


/-! ## General finite integer-combination certificates

The hypotheses express both inclusions of the integer submodules generated by
the generators and the actual differences. Neither mentions the functional.
-/

/-- General integer criterion: generators may be combinations of actual differences. -/
theorem integer_combination_criterion {n r : Nat} (d e₀ : Fin n → ℤ) (c : ℤ)
    (b : Fin r → Fin n → ℤ) (S : Set (Fin n → ℤ)) (he₀ : e₀ ∈ S)
    (hgen : ∀ e ∈ S, ∃ lam : Fin r → ℤ, e - e₀ = ∑ i, lam i • b i)
    (hmem : ∀ i, ∃ (m : Nat) (e : Fin m → Fin n → ℤ) (lam : Fin m → ℤ),
      (∀ k, e k ∈ S) ∧ b i = ∑ k, lam k • (e k - e₀)) :
    (∀ e ∈ S, dot d e + c = 0) ↔
      (dot d e₀ + c = 0 ∧ ∀ i, dot d (b i) = 0) := by
  constructor
  · intro h
    refine ⟨h e₀ he₀, fun i => ?_⟩
    obtain ⟨m, e, lam, he, hb⟩ := hmem i
    rw [hb, dot_sum]
    apply Finset.sum_eq_zero
    intro k _
    have hk := h (e k) (he k)
    have h₀ := h e₀ he₀
    have hz : dot d (e k - e₀) = 0 := by rw [dot_sub]; omega
    rw [hz, mul_zero]
  · rintro ⟨h₀, hb⟩ e he
    obtain ⟨lam, hlam⟩ := hgen e he
    have hdiff : dot d (e - e₀) = 0 := by
      rw [hlam, dot_sum]
      simp only [hb, mul_zero, Finset.sum_const_zero]
    rw [dot_sub] at hdiff
    omega

/-- The actual p-adic ledger criterion with general integer-span membership
certificates. Nonzero and base-point premises remain explicit. -/
theorem restricted_ledger_combination_criterion {n r : Nat} (Ω : Set (Tuple p n))
    (hΩ : ∀ x ∈ Ω, ∀ j, x j ≠ 0)
    (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0)
    (x₀ : Tuple p n) (hx₀ : x₀ ∈ Ω) (b : Fin r → Fin n → ℤ)
    (hgen : ∀ x ∈ Ω, ∃ lam : Fin r → ℤ,
      vprofile p x - vprofile p x₀ = ∑ i, lam i • b i)
    (hmem : ∀ i, ∃ (m : Nat) (x : Fin m → Tuple p n) (lam : Fin m → ℤ),
      (∀ k, x k ∈ Ω) ∧ b i = ∑ k, lam k • (vprofile p (x k) - vprofile p x₀)) :
    (∀ x ∈ Ω, weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
      dot (fun j => w (σ j) - w j) (vprofile p x₀)
          + ∑ j, w (σ j) * (a j).valuation = 0
        ∧ ∀ i, dot (fun j => w (σ j) - w j) (b i) = 0 := by
  have hc := integer_combination_criterion (fun j => w (σ j) - w j) (vprofile p x₀)
    (∑ j, w (σ j) * (a j).valuation) b (vprofile p '' Ω) ⟨x₀, hx₀, rfl⟩
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := he
      exact hgen x hx)
    (fun i => by
      obtain ⟨m, x, lam, hx, hb⟩ := hmem i
      exact ⟨m, fun k => vprofile p (x k), lam, fun k => ⟨x k, hx k, rfl⟩, hb⟩)
  rw [← hc]
  constructor
  · intro h e he
    obtain ⟨x, hx, rfl⟩ := he
    rw [← weightedLedger_shift p σ w a x ha (hΩ x hx), h x hx, sub_self]
  · intro h x hx
    have hz := h (vprofile p x) ⟨x, hx, rfl⟩
    rw [← weightedLedger_shift p σ w a x ha (hΩ x hx)] at hz
    exact sub_eq_zero.mp hz

/-- Full nonzero-domain iff derived from the general restricted certificate,
including the scalar budget as well as weight invariance. -/
theorem full_domain_iff {n : Nat} (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0) :
    (∀ x : Tuple p n, (∀ j, x j ≠ 0) →
      weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
      (∀ j, w (σ j) = w j) ∧ (∑ j, w (σ j) * (a j).valuation = 0) := by
  have hc := restricted_ledger_combination_criterion p (nonzeroDomain p n)
    (fun _ hx => hx) w σ a ha (fun _ : Fin n => (1 : ℚ_[p])) (nonzeroDomain_one_mem p)
    (fun i => fun j => if j = i then (1 : ℤ) else 0)
    (fun x hx => nonzeroDomain_span p hx)
    (fun i => by
      obtain ⟨x, hx, he⟩ := nonzeroDomain_realises_generator p i
      refine ⟨1, fun _ => x, fun _ => 1, fun _ => hx, ?_⟩
      simpa only [Fin.sum_univ_one, one_smul] using he.symm)
  simp only [nonzeroDomain, Set.mem_ofPred_eq] at hc
  rw [hc]
  simp only [vprofile_one_tuple, dot_single]
  have hz : dot (fun j => w (σ j) - w j) (fun _ => (0 : ℤ)) = 0 := by simp [dot]
  rw [hz, zero_add]
  constructor
  · rintro ⟨hbudget, hw⟩
    exact ⟨fun j => sub_eq_zero.mp (hw j), hbudget⟩
  · rintro ⟨hw, hbudget⟩
    exact ⟨hbudget, fun j => sub_eq_zero.mpr (hw j)⟩

/-- Finite domain with differences 0, 2, 3 from the base point 0. -/
def finiteIntegerDomain : Set (Fin 1 → ℤ) :=
  {e | e = (fun _ => 0) ∨ e = (fun _ => 2) ∨ e = (fun _ => 3)}

/-- Single generator 1, which is 3 - 2 but not an actual difference. -/
def integerUnitGenerator : Fin 1 → Fin 1 → ℤ := fun _ _ => 1

/-- Nonemptiness, both generation certificates, failure of realisation, and the
general integer criterion on the finite domain {0,2,3}. -/
theorem finite_integer_span_membership_example :
    (fun _ : Fin 1 => (0 : ℤ)) ∈ finiteIntegerDomain ∧
    (∀ e ∈ finiteIntegerDomain, ∃ lam : Fin 1 → ℤ,
      e - (fun _ => 0) = ∑ i, lam i • integerUnitGenerator i) ∧
    (∀ i : Fin 1, ∃ (m : Nat) (e : Fin m → Fin 1 → ℤ) (lam : Fin m → ℤ),
      (∀ k, e k ∈ finiteIntegerDomain) ∧
        integerUnitGenerator i = ∑ k, lam k • (e k - (fun _ => 0))) ∧
    (¬ ∃ e ∈ finiteIntegerDomain, e - (fun _ => 0) = integerUnitGenerator 0) ∧
    (∀ (d : Fin 1 → ℤ) (c : ℤ),
      (∀ e ∈ finiteIntegerDomain, dot d e + c = 0) ↔
        c = 0 ∧ ∀ i, dot d (integerUnitGenerator i) = 0) := by
  have h₀ : (fun _ : Fin 1 => (0 : ℤ)) ∈ finiteIntegerDomain := Or.inl rfl
  have hgen : ∀ e ∈ finiteIntegerDomain, ∃ lam : Fin 1 → ℤ,
      e - (fun _ => 0) = ∑ i, lam i • integerUnitGenerator i := by
    intro e _
    refine ⟨fun _ => e 0, ?_⟩
    funext j
    fin_cases j
    simp [integerUnitGenerator]
  have hmem : ∀ i : Fin 1, ∃ (m : Nat) (e : Fin m → Fin 1 → ℤ) (lam : Fin m → ℤ),
      (∀ k, e k ∈ finiteIntegerDomain) ∧
        integerUnitGenerator i = ∑ k, lam k • (e k - (fun _ => 0)) := by
    intro i
    refine ⟨2, (fun k _ => if k = 0 then 2 else 3),
      (fun k => if k = 0 then -1 else 1), ?_, ?_⟩
    · intro k
      fin_cases k <;> simp [finiteIntegerDomain]
    · funext j
      norm_num [Fin.sum_univ_two, integerUnitGenerator, Pi.sub_apply]
  refine ⟨h₀, hgen, hmem, ?_, ?_⟩
  · rintro ⟨e, he, heq⟩
    have hval := congrFun heq 0
    rcases he with rfl | rfl | rfl <;> norm_num [integerUnitGenerator] at hval
  · intro d c
    simpa only [dot, mul_zero, Finset.sum_const_zero, zero_add] using
      integer_combination_criterion d (fun _ => 0) c integerUnitGenerator
        finiteIntegerDomain h₀ hgen hmem


/-! ## The hierarchy of the two hypotheses

`hreal` (each generator is itself an actual difference) and `hmem` (each generator is
a finite integer combination of actual differences) are not equivalent, and only the
second is the hypothesis the task asks for. This section names that hypothesis and
proves the inclusion explicitly, so that the strong-premise criterion stands as a
candidate special case of the general span certificate instead of a separate
assumption.

The converse inclusion fails: `finite_integer_span_membership_example` exhibits a
finite set in which the generator lies in the difference span without being an actual
difference. -/

/-- `v` lies in the `ℤ`-span of the differences `e - e₀` with `e ∈ S`. The body
mentions only `S`, the base point and the generators; it never mentions a functional,
a weight vector or the ledger. -/
def MemDiffSpan {n : Nat} (S : Set (Fin n → ℤ)) (e₀ v : Fin n → ℤ) : Prop :=
  ∃ (m : Nat) (e : Fin m → Fin n → ℤ) (lam : Fin m → ℤ),
    (∀ k, e k ∈ S) ∧ v = ∑ k, lam k • (e k - e₀)

/-- The same span certificate for the actual `Q_p` ledger: `v` is a finite integer
combination of the profile differences `vprofile p x - vprofile p x₀` realised by
points of the restricted domain `Ω`. -/
def MemDiffSpanOn {n : Nat} (Ω : Set (Tuple p n)) (x₀ : Tuple p n)
    (v : Fin n → ℤ) : Prop :=
  ∃ (m : Nat) (x : Fin m → Tuple p n) (lam : Fin m → ℤ),
    (∀ k, x k ∈ Ω) ∧ v = ∑ k, lam k • (vprofile p (x k) - vprofile p x₀)

/-- A realised generator lies in the difference span: it is the one-term combination
of a single actual difference with coefficient `1`. -/
theorem memDiffSpan_of_realised {n r : Nat} (S : Set (Fin n → ℤ)) (e₀ : Fin n → ℤ)
    (b : Fin r → Fin n → ℤ) (hreal : ∀ i, ∃ e ∈ S, e - e₀ = b i) :
    ∀ i, MemDiffSpan S e₀ (b i) := by
  intro i
  obtain ⟨e, heS, hb⟩ := hreal i
  exact ⟨1, fun _ => e, fun _ => (1 : ℤ), fun _ => heS,
    by simpa only [Fin.sum_univ_one, one_smul] using hb.symm⟩

/-- A generator realised by an actual point of `Ω` lies in the point-level difference
span of `Ω`. -/
theorem memDiffSpanOn_of_realised {n r : Nat} (Ω : Set (Tuple p n)) (x₀ : Tuple p n)
    (b : Fin r → Fin n → ℤ)
    (hreal : ∀ i, ∃ x ∈ Ω, vprofile p x - vprofile p x₀ = b i) :
    ∀ i, MemDiffSpanOn p Ω x₀ (b i) := by
  intro i
  obtain ⟨x, hx, hb⟩ := hreal i
  exact ⟨1, fun _ => x, fun _ => (1 : ℤ), fun _ => hx,
    by simpa only [Fin.sum_univ_one, one_smul] using hb.symm⟩

/-- The strong-premise integer criterion is a corollary of the general combination
criterion: realisation is a one-term membership certificate. -/
theorem integer_span_criterion_of_combination {n r : Nat} (d e₀ : Fin n → ℤ) (c : ℤ)
    (b : Fin r → Fin n → ℤ) (S : Set (Fin n → ℤ)) (he₀ : e₀ ∈ S)
    (hgen : ∀ e ∈ S, ∃ lam : Fin r → ℤ, e - e₀ = ∑ i, lam i • b i)
    (hreal : ∀ i, ∃ e ∈ S, e - e₀ = b i) :
    (∀ e ∈ S, dot d e + c = 0) ↔ (dot d e₀ + c = 0 ∧ ∀ i, dot d (b i) = 0) :=
  integer_combination_criterion d e₀ c b S he₀ hgen
    (memDiffSpan_of_realised S e₀ b hreal)

/-- **The general span certificate version of the ledger criterion.** The premise
`hspan` asks only that every generator lies in the `ℤ`-span of the actual profile
differences realised inside `Ω`; no generator has to be an actual difference. This is
the version the task asks for; `restricted_ledger_criterion` remains available as the
candidate with the stronger realisation premise. -/
theorem restricted_ledger_span_criterion {n r : Nat} (Ω : Set (Tuple p n))
    (hΩ : ∀ x ∈ Ω, ∀ j, x j ≠ 0)
    (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0)
    (x₀ : Tuple p n) (hx₀ : x₀ ∈ Ω) (b : Fin r → Fin n → ℤ)
    (hgen : ∀ x ∈ Ω, ∃ lam : Fin r → ℤ, vprofile p x - vprofile p x₀ = ∑ i, lam i • b i)
    (hspan : ∀ i, MemDiffSpanOn p Ω x₀ (b i)) :
    (∀ x ∈ Ω, weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
      dot (fun j => w (σ j) - w j) (vprofile p x₀)
          + ∑ j, w (σ j) * (a j).valuation = 0
        ∧ ∀ i, dot (fun j => w (σ j) - w j) (b i) = 0 :=
  restricted_ledger_combination_criterion p Ω hΩ w σ a ha x₀ hx₀ b hgen hspan

/-- The stronger-premise ledger criterion is a corollary of the general span
certificate: a realised generator is a one-term span witness. -/
theorem restricted_ledger_criterion_of_combination {n r : Nat} (Ω : Set (Tuple p n))
    (hΩ : ∀ x ∈ Ω, ∀ j, x j ≠ 0)
    (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (a : Fin n → ℚ_[p]) (ha : ∀ j, a j ≠ 0)
    (x₀ : Tuple p n) (hx₀ : x₀ ∈ Ω) (b : Fin r → Fin n → ℤ)
    (hgen : ∀ x ∈ Ω, ∃ lam : Fin r → ℤ, vprofile p x - vprofile p x₀ = ∑ i, lam i • b i)
    (hreal : ∀ i, ∃ x ∈ Ω, vprofile p x - vprofile p x₀ = b i) :
    (∀ x ∈ Ω, weightedLedger p w (relabel p σ (slotwise p a x)) = weightedLedger p w x) ↔
      dot (fun j => w (σ j) - w j) (vprofile p x₀)
          + ∑ j, w (σ j) * (a j).valuation = 0
        ∧ ∀ i, dot (fun j => w (σ j) - w j) (b i) = 0 :=
  restricted_ledger_combination_criterion p Ω hΩ w σ a ha x₀ hx₀ b hgen
    (memDiffSpanOn_of_realised p Ω x₀ b hreal)


end

end Candidates.RestrictedLedger
