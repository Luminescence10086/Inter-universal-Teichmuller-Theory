/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Decomposition
import Mathlib.RingTheory.Invariant.Profinite

/-!
# Surjectivity of the decomposition map for rational points

Let `Ω / F` be an (infinite) Galois extension, `A ⊆ Ω` a valuation subring and
`V = A ∩ F` the valuation ring of `F` below it. The decomposition map
`D_A → Gal(κ(A) / κ(V))` is surjective. [AbsTopIII] Prop. 1.6(ii) and Prop. 1.8 (`T3`
l.1993, l.2061) use this for a `k`-rational point `x` of a curve: the decomposition group of a
place above `x` surjects onto `G_k`, so that `x` has a section `s_x : G_k → Π_U`.

We deduce it from Mathlib's `Ideal.Quotient.stabilizerHom_surjective_of_profinite` applied to the
integral closure `B` of `V` in `Ω` and its prime `Q = 𝔪_A ∩ B`. The new input is that the
stabiliser of `Q` is the decomposition group of `A`, i.e. that `A` is determined by its centre
`Q` on `B` (`le_of_valuation_lt_one_imp`): if `A, A'` are valuation subrings of `Ω` over `V`
such that every element of `B` in `𝔪_{A'}` lies in `𝔪_A`, then `A ≤ A'`. The proof uses
Kaplansky's lemma on the integrality of the partial sums `c_n x^k + ⋯ + c_{n-k}` of a relation
`∑ c_i x^i = 0` (`isIntegral_partialSum`), applied to a relation of `x` over `V` normalised so
that some coefficient is a unit.

## Main results

* `KummerTheory.Decomposition.isIntegral_partialSum` (Kaplansky's lemma);
* `KummerTheory.Decomposition.le_of_valuation_lt_one_imp`: a valuation subring of an algebraic
  extension is determined by its centre on the integral closure of the base valuation ring;
* `KummerTheory.Decomposition.exists_decompositionMap_eq_of_fixes`: the image of
  `D_A → Gal(κ(A)/k)` contains every `τ` trivial on the residues of `A ∩ F`;
* `KummerTheory.Decomposition.decompositionMap_surjective`: for `Ω` algebraically closed and
  `κ(A ∩ F) = k` (a `k`-rational point), `D_A → Gal(κ(A) / k)` is surjective.
-/

open Polynomial IsLocalRing

namespace KummerTheory

namespace Decomposition

section Kaplansky

variable {R Ω : Type*} [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- If `∑_{i ≤ n} c_i x^i = 0` with all `c_i` integral over `R`, then the leading coefficient
times `x` is integral over `R`. -/
theorem isIntegral_mul_of_sum_eq_zero (x : Ω) (n : ℕ) (c : ℕ → Ω)
    (hc : ∀ i, IsIntegral R (c i)) (h : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    IsIntegral R (c n * x) := by
  set C := integralClosure R Ω
  by_cases hn : c n = 0
  · rw [hn, zero_mul]
    exact isIntegral_zero
  let p : C[X] := ∑ i ∈ Finset.range (n + 1), monomial i (⟨c i, hc i⟩ : C)
  have hcoeff : ∀ j, j ≤ n → p.coeff j = ⟨c j, hc j⟩ := by
    intro j hj
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single j (fun b _ hb => ite_eq_right hb)
      (fun h' => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h'), ite_eq_left rfl]
  have hzero : ∀ j, n < j → p.coeff j = 0 := by
    intro j hj
    simp only [p, finsetSum_coeff, coeff_monomial]
    refine Finset.sum_eq_zero fun b hb => ite_eq_right ?_
    have := Finset.mem_range.mp hb
    omega
  have hdeg : p.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      exact hzero j (by exact_mod_cast hj)
    · rw [hcoeff n le_rfl]
      exact fun h => hn (congrArg Subtype.val h)
  have hlead : p.leadingCoeff = ⟨c n, hc n⟩ := by
    rw [leadingCoeff, hdeg, hcoeff n le_rfl]
  have haeval : aeval x p = 0 := by
    simp only [p, map_sum, aeval_monomial]
    rw [← h]
    rfl
  have h1 := isIntegral_leadingCoeff_smul p x haeval
  rw [hlead] at h1
  exact isIntegral_trans _ h1

/-- **Kaplansky's lemma.** If `∑_{i ≤ n} c_i x^i = 0` with all `c_i` integral over `R`, then
for every `k ≤ n` the partial sum `c_n x^k + c_{n-1} x^{k-1} + ⋯ + c_{n-k}` is integral
over `R`. -/
theorem isIntegral_partialSum (x : Ω) (k : ℕ) : ∀ (n : ℕ) (c : ℕ → Ω),
    (∀ i, IsIntegral R (c i)) → ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 → k ≤ n →
    IsIntegral R (∑ i ∈ Finset.range (k + 1), c (n - i) * x ^ (k - i)) := by
  induction k with
  | zero =>
    intro n c hc _ _
    simpa using hc n
  | succ k ih =>
    intro n c hc h hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set c' := Function.update c m (c (m + 1) * x + c m) with hc'
    have hc'int : ∀ i, IsIntegral R (c' i) := by
      intro i
      by_cases hi : i = m
      · rw [hi, hc', Function.update_self]
        exact (isIntegral_mul_of_sum_eq_zero x (m + 1) c hc h).add (hc m)
      · rw [hc', Function.update_of_ne hi]
        exact hc i
    have hrel : ∑ i ∈ Finset.range (m + 1), c' i * x ^ i = 0 := by
      rw [← h, Finset.sum_range_succ, Finset.sum_range_succ (n := m + 1), Finset.sum_range_succ]
      have hlow : ∑ i ∈ Finset.range m, c' i * x ^ i = ∑ i ∈ Finset.range m, c i * x ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hc', Function.update_of_ne (Finset.mem_range.mp hi).ne]
      rw [hlow, hc', Function.update_self]
      ring
    have := ih m c' hc'int hrel (by omega)
    have e1 : ∑ i ∈ Finset.range (k + 1 + 1), c (m + 1 - i) * x ^ (k + 1 - i) =
        ∑ i ∈ Finset.range k, c (m - (i + 1)) * x ^ (k - (i + 1)) + c m * x ^ k +
          c (m + 1) * x ^ (k + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      congr 2
      · refine Finset.sum_congr rfl fun i hi => ?_
        congr 2 <;> omega
    have e2 : ∑ i ∈ Finset.range (k + 1), c' (m - i) * x ^ (k - i) =
        ∑ i ∈ Finset.range k, c (m - (i + 1)) * x ^ (k - (i + 1)) +
          (c (m + 1) * x + c m) * x ^ k := by
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [hc', Function.update_of_ne (by have := Finset.mem_range.mp hi; omega)]
      · rw [Nat.sub_zero, Nat.sub_zero, hc', Function.update_self]
    rw [e1]
    rw [e2] at this
    convert this using 1
    ring

end Kaplansky

section Valuation

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- An algebraic element `x` satisfies a relation `∑_{i ≤ n} a_i x^i = 0` with coefficients in a
given valuation subring `V` of `F`, one of which is `1`. -/
theorem exists_sum_eq_zero_of_isAlgebraic (V : ValuationSubring F) {x : Ω}
    (hx : IsAlgebraic F x) :
    ∃ (n : ℕ) (a : ℕ → F), (∀ i, a i ∈ V) ∧ (∃ j ≤ n, a j = 1) ∧
      ∑ i ∈ Finset.range (n + 1), algebraMap F Ω (a i) * x ^ i = 0 := by
  obtain ⟨p, hp0, hp⟩ := hx
  set n := p.natDegree
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => V.valuation (p.coeff i)) ⟨n, Finset.self_mem_range_succ n⟩
  have hpm : p.coeff m ≠ 0 := by
    intro h0
    have := hmax n (Finset.self_mem_range_succ n)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hp0 (leadingCoeff_eq_zero.mp this)
  refine ⟨n, fun i => p.coeff i / p.coeff m, fun i => ?_,
    ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), div_self hpm⟩, ?_⟩
  · rw [← V.valuation_le_one_iff, map_div₀]
    by_cases hi : i ≤ n
    · exact div_le_one_of_le₀ (hmax i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) zero_le
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), map_zero, zero_div]
      exact zero_le
  · have h1 : aeval x p = ∑ i ∈ Finset.range (n + 1), algebraMap F Ω (p.coeff i) * x ^ i := by
      rw [aeval_eq_sum_range]
      simp_rw [Algebra.smul_def]
      rfl
    have h2 : ∑ i ∈ Finset.range (n + 1), algebraMap F Ω (p.coeff i / p.coeff m) * x ^ i =
        (∑ i ∈ Finset.range (n + 1), algebraMap F Ω (p.coeff i) * x ^ i) *
          algebraMap F Ω (p.coeff m)⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv, map_mul]
      ring
    rw [h2, ← h1, hp, zero_mul]

variable [Algebra.IsAlgebraic F Ω]

/-- **A valuation subring is determined by its centre on the integral closure.** Let `Ω / F` be
algebraic, `A, A'` valuation subrings of `Ω` with `A ∩ F ⊆ A'`, and suppose that every element
of `Ω` integral over `V = A ∩ F` which lies in the maximal ideal of `A'` lies in the maximal ideal
of `A`. Then `A ≤ A'`.

Proof: for `x ∈ A \ A'` take a relation `∑ a_i x^i = 0` over `V` with a coefficient equal to `1`
and let `j` be the largest index with `a_j` a unit of `A`. By Kaplansky's lemma
`z = a_j + a_{j+1} x + ⋯ + a_n x^{n-j}` is integral over `V`; it is a unit of `A`, but
`z = -∑_{i<j} a_i (x⁻¹)^{j-i}` lies in the maximal ideal of `A'`. -/
theorem le_of_valuation_lt_one_imp {A A' : ValuationSubring Ω}
    (hA' : ∀ a : F, algebraMap F Ω a ∈ A → algebraMap F Ω a ∈ A')
    (h : ∀ z : Ω, IsIntegral (A.comap (algebraMap F Ω)) z → A'.valuation z < 1 →
      A.valuation z < 1) :
    A ≤ A' := by
  intro x hx
  by_contra hx'
  have hx0 : x ≠ 0 := fun h0 => hx' (h0 ▸ A'.zero_mem)
  have hxinv : A'.valuation x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (not_le.mp fun h' => hx' ((A'.valuation_le_one_iff x).mp h'))
  set V := A.comap (algebraMap F Ω)
  obtain ⟨n, a, haV, ⟨j₀, hj₀n, hj₀⟩, hrel⟩ :=
    exists_sum_eq_zero_of_isAlgebraic V (Algebra.IsAlgebraic.isAlgebraic (R := F) x)
  set c : ℕ → Ω := fun i => algebraMap F Ω (a i) with hc
  have hcA : ∀ i, A.valuation (c i) ≤ 1 := fun i => (A.valuation_le_one_iff _).mpr (haV i)
  have hcA' : ∀ i, A'.valuation (c i) ≤ 1 := fun i =>
    (A'.valuation_le_one_iff _).mpr (hA' _ (haV i))
  classical
  set U := (Finset.range (n + 1)).filter (fun i => A.valuation (c i) = 1)
  have hU : U.Nonempty := ⟨j₀, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj₀n), by simp [c, hj₀]⟩⟩
  set j := U.max' hU
  have hjU : j ∈ U := U.max'_mem hU
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjU).1)
  have hj1 : A.valuation (c j) = 1 := (Finset.mem_filter.mp hjU).2
  have hgt : ∀ i, j < i → i ≤ n → A.valuation (c i) < 1 := by
    intro i hji hin
    refine lt_of_le_of_ne (hcA i) fun h1 => ?_
    have : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hin), h1⟩
    exact absurd (U.le_max' i this) (not_le.mpr hji)
  set z := ∑ i ∈ Finset.range (n - j + 1), c (j + i) * x ^ i with hz
  -- `z` is integral over `V` (Kaplansky)
  have hzint : IsIntegral V z := by
    have hcint : ∀ i, IsIntegral V (c i) := fun i =>
      isIntegral_algebraMap (R := V) (x := (⟨a i, haV i⟩ : V))
    have := isIntegral_partialSum x (n - j) n c hcint hrel (Nat.sub_le n j)
    have e : z = ∑ i ∈ Finset.range (n - j + 1), c (n - i) * x ^ (n - j - i) := by
      rw [hz, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      congr 2
      omega
    rw [e]
    exact this
  -- `z` is a unit of `A`
  have hzA : ¬ A.valuation z < 1 := by
    have hsplit : z = (∑ i ∈ Finset.range (n - j), c (j + (i + 1)) * x ^ (i + 1)) + c j := by
      rw [hz, Finset.sum_range_succ', pow_zero, mul_one, add_zero]
    have hrest : A.valuation (∑ i ∈ Finset.range (n - j), c (j + (i + 1)) * x ^ (i + 1)) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      have := Finset.mem_range.mp hi
      rw [map_mul, map_pow]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hgt _ (by omega) (by omega))
        (pow_le_one₀ zero_le ((A.valuation_le_one_iff x).mpr hx))
    rw [hsplit, Valuation.map_add_eq_of_lt_right _ (hj1 ▸ hrest), hj1]
    exact lt_irrefl 1
  -- `z` lies in the maximal ideal of `A'`
  have hzA' : A'.valuation z < 1 := by
    have hsum : ∑ i ∈ Finset.range (n + 1), c i * x ^ i =
        ∑ i ∈ Finset.range j, c i * x ^ i + x ^ j * z := by
      rw [show n + 1 = j + (n - j + 1) by omega, Finset.sum_range_add, hz, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]
      ring
    rw [hrel] at hsum
    have hz' : z = -∑ i ∈ Finset.range j, c i * x⁻¹ ^ (j - i) := by
      have hxj : x ^ j ≠ 0 := pow_ne_zero j hx0
      have : z = -(∑ i ∈ Finset.range j, c i * x ^ i) * (x⁻¹) ^ j := by
        rw [inv_pow, eq_mul_inv_iff_mul_eq₀ hxj]
        linear_combination -hsum
      rw [this, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i ≤ j := (Finset.mem_range.mp hi).le
      rw [mul_assoc]
      congr 1
      rw [← Nat.sub_add_cancel hij, pow_add, Nat.sub_add_cancel hij, inv_pow x i]
      field_simp
    rw [hz', Valuation.map_neg]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have := Finset.mem_range.mp hi
    rw [map_mul, map_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hcA' i) zero_le
      (pow_lt_one₀ zero_le hxinv (by omega))
  exact hzA (h z hzint hzA')

end Valuation

section Surjective

open scoped Pointwise

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)

/-- Elements of `Ω` integral over `A ∩ F` lie in `A`. -/
theorem mem_of_isIntegral_comap {z : Ω} (hz : IsIntegral (A.comap (algebraMap F Ω)) z) :
    z ∈ A := by
  let φ : A.comap (algebraMap F Ω) →+* A :=
    { toFun := fun v => ⟨algebraMap F Ω v, v.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hz' : IsIntegral A z := hz.map_of_comp_eq φ (RingHom.id Ω) (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz'
  rw [← hy]
  exact y.2

/-- `x ∈ g • A ↔ g⁻¹ x ∈ A` for `g ∈ Gal(Ω/F)`. -/
theorem mem_smul_iff (g : Ω ≃ₐ[F] Ω) (x : Ω) : x ∈ g • A ↔ g⁻¹ x ∈ A := by
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [AlgEquiv.smul_def] using hs
  · intro h
    exact ⟨g⁻¹ x, h, by simp [AlgEquiv.smul_def]⟩

/-- `v_{g • A}(x) < 1 ↔ v_A(g⁻¹ x) < 1`. -/
theorem valuation_smul_lt_one_iff (g : Ω ≃ₐ[F] Ω) (x : Ω) :
    (g • A).valuation x < 1 ↔ A.valuation (g⁻¹ x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_smul_iff,
    map_inv₀, map_eq_zero_iff _ (g⁻¹).injective]

variable (F) in
/-- The inclusion of the integral closure `B` of `A ∩ F` in `Ω` into `A`. -/
noncomputable def integralClosureToA :
    integralClosure (A.comap (algebraMap F Ω)) Ω →+* A :=
  (integralClosure (A.comap (algebraMap F Ω)) Ω).val.toRingHom.codRestrict A.toSubring
    fun b => mem_of_isIntegral_comap A b.2

variable (F) in
/-- The centre `Q = 𝔪_A ∩ B` of `A` on the integral closure `B` of `A ∩ F` in `Ω`. -/
noncomputable def centre : Ideal (integralClosure (A.comap (algebraMap F Ω)) Ω) :=
  (maximalIdeal A).comap (integralClosureToA F A)

variable (F) in
theorem mem_centre_iff (b : integralClosure (A.comap (algebraMap F Ω)) Ω) :
    b ∈ centre F A ↔ A.valuation (b : Ω) < 1 := by
  rw [centre, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

variable (F) in
instance isPrime_centre : (centre F A).IsPrime := Ideal.comap_isPrime _ _

variable [Algebra.IsAlgebraic F Ω]

/-- Elements of `Gal(Ω/F)` stabilising the centre `Q` satisfy `A ≤ g • A`. -/
theorem le_smul_of_smul_centre (g : Ω ≃ₐ[F] Ω) (hg : g • centre F A = centre F A) :
    A ≤ g • A := by
  refine le_of_valuation_lt_one_imp (F := F) (fun a ha => ?_) fun z hz hzg => ?_
  · rw [mem_smul_iff, AlgEquiv.commutes]
    exact ha
  · rw [valuation_smul_lt_one_iff] at hzg
    let b : integralClosure (A.comap (algebraMap F Ω)) Ω := ⟨z, hz⟩
    have hb : g⁻¹ • b ∈ centre F A := (mem_centre_iff F A _).mpr hzg
    rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hg] at hb
    exact (mem_centre_iff F A b).mp hb

/-- **The stabiliser of the centre is the decomposition group.** -/
theorem mem_decompositionSubgroup_of_smul_centre (g : Ω ≃ₐ[F] Ω)
    (hg : g • centre F A = centre F A) : g ∈ A.decompositionSubgroup F := by
  have hg' : g⁻¹ • centre F A = centre F A := by
    rw [inv_smul_eq_iff, hg]
  have h1 := le_smul_of_smul_centre A g hg
  have h2 := le_smul_of_smul_centre A g⁻¹ hg'
  refine MulAction.mem_stabilizer_iff.mpr (le_antisymm (fun x hx => ?_) h1)
  rw [mem_smul_iff] at hx
  have := (mem_smul_iff A g⁻¹ _).mp (h2 hx)
  simpa using this

end Surjective

section Rational

open scoped Pointwise

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

variable (F) in
include hkres in
/-- Over an algebraically closed `Ω`, every residue class of `A` algebraic over `k ⊆ A ∩ F` is
the residue of an element of the integral closure `B` of `A ∩ F`: if `g` is a monic polynomial
over `k` killing `y = ā`, then `g(a) = ∏ (a - r)` over the roots `r ∈ B` of `g`, and `g(a) ∈ 𝔪_A`
forces `a ≡ r mod 𝔪_A` for some root `r`. -/
theorem exists_residue_integralClosureToA_eq [IsAlgClosed Ω] (y : ResidueField A)
    (hy : IsIntegral k y) :
    ∃ b : integralClosure (A.comap (algebraMap F Ω)) Ω,
      residue A (integralClosureToA F A b) = y := by
  obtain ⟨g, hmonic, hg⟩ := hy
  set gΩ := g.map (algebraMap k Ω)
  have hprod : gΩ = (gΩ.roots.map (X - C ·)).prod := by
    have := (IsAlgClosed.splits gΩ).eq_prod_roots
    rwa [(hmonic.map _).leadingCoeff, C_1, one_mul] at this
  let φk : k →+* A.comap (algebraMap F Ω) :=
    (algebraMap k F).codRestrict (A.comap (algebraMap F Ω)).toSubring fun c => by
      change algebraMap F Ω (algebraMap k F c) ∈ A
      rw [← IsScalarTower.algebraMap_apply]
      exact hk c
  have hφk : (algebraMap (A.comap (algebraMap F Ω)) Ω).comp φk = algebraMap k Ω :=
    RingHom.ext fun c => (IsScalarTower.algebraMap_apply k F Ω c).symm
  have hint : ∀ r ∈ gΩ.roots, IsIntegral (A.comap (algebraMap F Ω)) r := by
    intro r hr
    refine ⟨g.map φk, hmonic.map _, ?_⟩
    rw [eval₂_map, hφk]
    have := (mem_roots (hmonic.map _).ne_zero).mp hr
    rw [IsRoot.def, eval_map] at this
    exact this
  -- lift `y` to `a ∈ A`
  obtain ⟨a, rfl⟩ := residue_surjective y
  let ψk : k →+* A := (algebraMap k Ω).codRestrict A.toSubring hk
  have hgA : ((eval a (g.map ψk) : A) : Ω) = eval (a : Ω) gΩ := by
    rw [eval_map, eval_map]
    change A.toSubring.subtype (eval₂ ψk a g) = _
    rw [hom_eval₂]
    rfl
  have hgres : residue A (eval a (g.map ψk)) = 0 := by
    rw [eval_map, hom_eval₂, ← hg]
    congr 1
    exact RingHom.ext fun c => hkres c
  have hlt : A.valuation (eval (a : Ω) gΩ) < 1 := by
    rw [← hgA]
    exact (A.valuation_lt_one_iff _).mp ((residue_eq_zero_iff _).mp hgres)
  rw [hprod, eval_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map] at hlt
  by_contra hne
  simp only [not_exists] at hne
  refine absurd hlt (not_lt.mpr (le_of_eq (Multiset.prod_eq_one fun v hv => ?_).symm))
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hv
  have hrA : r ∈ A := mem_of_isIntegral_comap A (hint r hr)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  refine le_antisymm ((A.valuation_le_one_iff _).mpr (A.sub_mem a.2 hrA)) (not_lt.mp fun h => ?_)
  apply hne ⟨r, hint r hr⟩
  have hm : a - integralClosureToA F A ⟨r, hint r hr⟩ ∈ maximalIdeal A :=
    (A.valuation_lt_one_iff _).mpr h
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rw [← neg_sub]
  exact neg_mem hm

variable [IsGalois F Ω]

include hkres in
/-- **The image of the decomposition map is `Gal(κ(A)/κ(A ∩ F))`.** Let `Ω / F` be Galois with
`Ω` algebraically closed, `A ⊆ Ω` a valuation subring containing `k ⊆ F`, with `κ(A)` algebraic
over `k`. Every `τ ∈ Gal(κ(A)/k)` fixing the residues of the elements of `A ∩ F` (i.e. trivial
on the residue field `κ(A ∩ F) ⊆ κ(A)`) is the image of an element of the decomposition group
`D_A`. For a curve over `k` and a place `A` above a closed point `x`, this identifies the image
of `D_A` with `G_{k_x} = Gal(κ(A)/k_x)`. -/
theorem exists_decompositionMap_eq_of_fixes [IsAlgClosed Ω]
    [Algebra.IsIntegral k (ResidueField A)] (τ : Gal(ResidueField A/k))
    (hτ : ∀ (a : F) (ha : algebraMap F Ω a ∈ A), τ (residue A ⟨_, ha⟩) = residue A ⟨_, ha⟩) :
    ∃ σ, decompositionMap F A hk hkres σ = τ := by
  set V := A.comap (algebraMap F Ω)
  set B := integralClosure V Ω
  set Q := centre F A
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[F] Ω) B := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    convert stabilizer_isOpen_of_isIntegral (K := F) (b : Ω) using 2
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  have : Algebra.IsInvariant V B (Ω ≃ₐ[F] Ω) := by
    refine ⟨fun b hb => ?_⟩
    obtain ⟨f, hf⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : Ω)).mpr fun g =>
      congrArg Subtype.val (hb g)
    have hfint : IsIntegral V f := by
      rw [← isIntegral_algebraMap_iff (R := V) (A := F) (B := Ω), hf]
      exact b.2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hfint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hf, ← hv]
    rfl
  have : Q.LiesOver (Q.under V) := ⟨rfl⟩
  -- the identification `B ⧸ Q ≃ κ(A)`
  let ψ : B ⧸ Q →+* ResidueField A := Ideal.Quotient.lift Q
    ((residue A).comp (integralClosureToA F A)) fun b hb => (residue_eq_zero_iff _).mpr hb
  have hψinj : Function.Injective ψ := by
    rw [Ideal.injective_lift_iff, ← RingHom.comap_ker, ker_residue]
    rfl
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨b, hb⟩ := exists_residue_integralClosureToA_eq F A hk hkres y
      (Algebra.IsIntegral.isIntegral y)
    exact ⟨Ideal.Quotient.mk Q b, hb⟩
  let e : B ⧸ Q ≃+* ResidueField A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = residue A (integralClosureToA F A b) :=
    fun _ => rfl
  let τ' : (B ⧸ Q) ≃ₐ[V ⧸ Q.under V] (B ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (e.trans τ.toRingEquiv).trans e.symm) fun x => by
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
      change e.symm (τ (e (Ideal.Quotient.mk Q (algebraMap V B v)))) = _
      rw [he]
      have : residue A (integralClosureToA F A (algebraMap V B v)) =
          residue A ⟨_, v.2⟩ := rfl
      erw [this, hτ, ← this, ← he, RingEquiv.symm_apply_apply]
      rfl
  obtain ⟨⟨σ, hσ⟩, hστ⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[F] Ω) (Q.under V) Q τ'
  refine ⟨⟨σ, mem_decompositionSubgroup_of_smul_centre A σ hσ⟩, AlgEquiv.ext fun y => ?_⟩
  obtain ⟨b, rfl⟩ := exists_residue_integralClosureToA_eq F A hk hkres y
    (Algebra.IsIntegral.isIntegral y)
  rw [decompositionMap_residue]
  have h1 : τ (e (Ideal.Quotient.mk Q b)) = e (τ' (Ideal.Quotient.mk Q b)) := by
    change _ = e (e.symm (τ (e _)))
    rw [RingEquiv.apply_symm_apply]
  rw [← he, h1, ← hστ, Ideal.Quotient.stabilizerHom_apply, he]
  rfl

include hkres in
/-- **Surjectivity of the decomposition map for rational points.** Let `Ω / F` be Galois with
`Ω` algebraically closed, `A ⊆ Ω` a valuation subring containing `k ⊆ F`, with `κ(A)` algebraic
over `k` and `κ(A ∩ F) = k` (`hres`: every element of `A ∩ F` has a residue in `k`; for a curve
over `k` and a place `A` above a point `x`, this says that `x` is `k`-rational). Then the
decomposition map `D_A → Gal(κ(A)/k)` is surjective. -/
theorem decompositionMap_surjective [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
    (hres : ∀ (a : F) (ha : algebraMap F Ω a ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) :
    Function.Surjective (decompositionMap F A hk hkres) := fun τ =>
  exists_decompositionMap_eq_of_fixes (F := F) A hk hkres τ fun a ha => by
    obtain ⟨c, hc⟩ := hres a ha
    rw [hc, AlgEquiv.commutes]

end Rational

end Decomposition

end KummerTheory
