/-
# M2 candidate: orbit rectangles in a finite local quotient ring

This file is a *candidate* implementation for task M2 of the frozen
`handoffs/next-round` contract.  Nothing here is admitted to any fact tree.

Setting: `p` prime, `N n : ℕ`, the finite local ring `R = ZMod (p^N)`, and a
threshold vector `k : Fin n → ℕ` with `0 ≤ k j ≤ N`.  The coordinate box

  `B k = { x : Fin n → R | ∀ j, x j ∈ Ideal.span {(p : R) ^ (k j)} }`

is realized by the explicit `p`-divisibility predicate on representatives
(`Box`); `IdealBox_eq_Box` proves the two descriptions agree.  `Γ` is an
*explicitly finite* family of coordinate permutations containing the identity;
`U` is the union of the permuted boxes and `H` the smallest coordinate product
box containing `U`.

Main theorems, one per required case id:

* `hull_thresholds`     (M2.rectangular_hull_thresholds) — the hull thresholds
                          are the coordinatewise minima of the permuted
                          thresholds, each attained inside `Γ`.
* `hull_minimal`        (M2.rectangular_hull_minimality) — `H` contains `U`
                          and is minimal among coordinate boxes containing `U`.
* `box_cardinality`     (M2.box_cardinality) — `Nat.card (B k) = p ^ ∑ j, (N - k j)`.
* `enlargement_budget`  (M2.enlargement_integer_budget) — exact integer-exponent
                          budget `|B k| * p ^ e = |B k'|` for `k' ≤ k`.
* `two_three_four`      (M2.two_three_four_example) — the concrete
                          `p = 2, N = 1, n = 2, k = (0,1)`, `Γ = {id, swap}`
                          check: `2`, `3`, `4`.

Scope statements (deliberate limitations, see `SUMMARY.md`):

* Finite counting here is **not** a log-volume.  No Haar or Arakelov measure is
  introduced, and no function called `cost` is defined and called a volume.
* `Γ` is a finite *family* of permutations; it is not assumed to be a group and
  is not claimed to be induced by any Ind3 action.
* The global error budget, and the real seed / κ / σ identities of the actual
  IUT setting, remain **independent obligations** untouched by this file.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Ideal.Basic

set_option autoImplicit false

namespace OrbitQuotient

/-! ## 1. Boxes, ideals, and the coordinate action -/

/-- The threshold box, written as an explicit `p`-divisibility condition on the
canonical representative in `[0, p^N)` of each coordinate. -/
def Box (p N n : ℕ) (k : Fin n → ℕ) : Set (Fin n → ZMod (p ^ N)) :=
  {x | ∀ j, p ^ (k j) ∣ (x j).val}

/-- The same box written with ideals, i.e. literally the definition in the task
statement.  `IdealBox_eq_Box` shows the two agree (for `p` prime, `k ≤ N`). -/
def IdealBox (p N n : ℕ) (k : Fin n → ℕ) : Set (Fin n → ZMod (p ^ N)) :=
  {x | ∀ j, x j ∈ Ideal.span {(p : ZMod (p ^ N)) ^ (k j)}}

/-- The coordinate permutation action.  We fix the convention
`(γ • x) j = x (γ j)`, i.e. `γ • x = x ∘ γ`.  Consequently the `γ`-image of the
box `B k` is the box with thresholds `j ↦ k (γ⁻¹ j)`; see `mem_permAct_box`.
This is the σ/σ⁻¹ convention used everywhere below, including `hullThresh`. -/
def permAct (p N : ℕ) {n : ℕ} (γ : Equiv.Perm (Fin n))
    (x : Fin n → ZMod (p ^ N)) : Fin n → ZMod (p ^ N) :=
  fun j => x (γ j)

/-- The orbit union `U = ⋃_{γ ∈ Γ} γ • B k`, for an explicitly finite family `Γ`.
No group structure on `Γ` is assumed or used. -/
def orbitUnion (p N n : ℕ) (Γ : Finset (Equiv.Perm (Fin n)))
    (k : Fin n → ℕ) : Set (Fin n → ZMod (p ^ N)) :=
  {x | ∃ γ ∈ Γ, permAct p N γ x ∈ Box p N n k}

/-- The threshold vector of the minimal coordinate box containing the orbit
union: coordinate `j` gets the minimum of `k (γ⁻¹ j)` over `γ ∈ Γ`. -/
def hullThresh {n : ℕ} (Γ : Finset (Equiv.Perm (Fin n))) (hΓ : Γ.Nonempty)
    (k : Fin n → ℕ) : Fin n → ℕ :=
  fun j => (Γ.image (fun γ => k (γ.symm j))).min' (hΓ.image _)

/-! ## 2. Arithmetic of `p`-power thresholds in `ZMod (p^N)` -/

/-- `p ^ k * p ^ (N - k) = p ^ N` for `k ≤ N`. -/
lemma pow_mul_pow_sub {p k N : ℕ} (hk : k ≤ N) : p ^ k * p ^ (N - k) = p ^ N := by
  rw [← pow_add]
  congr 1
  omega

/-- For `1 < p`, an exponent is recovered from a divisibility of prime powers. -/
lemma le_of_pow_dvd_pow {p a b : ℕ} (hp : 1 < p) (h : p ^ a ∣ p ^ b) : a ≤ b := by
  by_contra hle
  rw [not_le] at hle
  have hpos : 0 < p ^ b := pow_pos (by omega) b
  have h1 : p ^ a ≤ p ^ b := Nat.le_of_dvd hpos h
  have h2 : p ^ b < p ^ a := Nat.pow_lt_pow_right hp hle
  omega

/-- The canonical representative of a `p`-power multiple inside `ZMod (p^N)`. -/
lemma val_pow_natCast {p N k : ℕ} : ((p : ZMod (p ^ N)) ^ k).val = p ^ k % p ^ N := by
  rw [← Nat.cast_pow, ZMod.val_natCast]

/-- In `ZMod (p^N)`, divisibility by `(p : R)^k` and divisibility of the
canonical representative by `p^k` agree, for `k ≤ N`. -/
lemma dvd_iff_val_dvd {p N : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≤ N)
    (x : ZMod (p ^ N)) : (p : ZMod (p ^ N)) ^ k ∣ x ↔ p ^ k ∣ x.val := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  constructor
  · rintro ⟨c, hc⟩
    rw [hc, ZMod.val_mul, val_pow_natCast]
    have h1 : p ^ k ∣ p ^ N := pow_dvd_pow p hk
    have h2 : p ^ k ∣ p ^ k % p ^ N := (Nat.dvd_mod_iff h1).mpr dvd_rfl
    exact (Nat.dvd_mod_iff h1).mpr (dvd_mul_of_dvd_left h2 c.val)
  · rintro ⟨m, hm⟩
    refine ⟨(m : ZMod (p ^ N)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, hm, Nat.cast_mul]

/-- The ideal-span box of the task statement equals the explicit divisibility
box. -/
theorem IdealBox_eq_Box {p N n : ℕ} (hp : p.Prime) (k : Fin n → ℕ)
    (hkN : ∀ j, k j ≤ N) : IdealBox p N n k = Box p N n k := by
  ext x
  simp only [IdealBox, Box, Ideal.mem_span_singleton]
  exact forall_congr' (fun j => dvd_iff_val_dvd hp (hkN j) (x j))

/-! ## 3. Stage 1: hull thresholds and minimality -/

/-- Raising the thresholds shrinks the box. -/
lemma box_mono {p N n : ℕ} {k k' : Fin n → ℕ} (h : ∀ j, k' j ≤ k j) :
    Box p N n k ⊆ Box p N n k' :=
  fun _ hx j => (pow_dvd_pow p (h j)).trans (hx j)

/-- The `γ`-image of `B k` is `B (j ↦ k (γ⁻¹ j))`.  This is the σ/σ⁻¹
direction fixing lemma. -/
lemma mem_permAct_box {p N n : ℕ} (γ : Equiv.Perm (Fin n)) (k : Fin n → ℕ)
    (x : Fin n → ZMod (p ^ N)) :
    permAct p N γ x ∈ Box p N n k ↔ x ∈ Box p N n (fun j => k (γ.symm j)) := by
  constructor
  · intro h j
    have h' := h (γ.symm j)
    simpa [permAct] using h'
  · intro h j
    have h' := h (γ j)
    simpa [permAct] using h'

/-- Extracting the threshold order from an inclusion of boxes, using the
coordinate witness `p ^ (k j)` placed in coordinate `j`. -/
lemma le_of_box_subset {p N n : ℕ} (hp : p.Prime) {k k' : Fin n → ℕ}
    (hkN : ∀ j, k j ≤ N) (hk'N : ∀ j, k' j ≤ N)
    (hsub : Box p N n k ⊆ Box p N n k') : ∀ j, k' j ≤ k j := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  intro j
  have hmem : Function.update (0 : Fin n → ZMod (p ^ N)) j
        ((p ^ (k j) : ℕ) : ZMod (p ^ N)) ∈ Box p N n k := by
    intro i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, ZMod.val_natCast]
      exact (Nat.dvd_mod_iff (pow_dvd_pow p (hkN i))).mpr dvd_rfl
    · simp [Function.update_of_ne hi]
  have hcon : p ^ (k' j) ∣ p ^ (k j) % p ^ N := by
    have h' := hsub hmem j
    rwa [Function.update_self, ZMod.val_natCast] at h'
  by_cases hN : k j = N
  · rw [hN]
    exact hk'N j
  · have hlt : k j < N := by
      have := hkN j
      omega
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp.one_lt hlt)] at hcon
    exact le_of_pow_dvd_pow hp.one_lt hcon

/-- **M2.rectangular_hull_thresholds.**  The hull thresholds are the
coordinatewise minima of the permuted thresholds, and each minimum is attained
inside the finite family `Γ`. -/
theorem hull_thresholds {n : ℕ} (Γ : Finset (Equiv.Perm (Fin n))) (hΓ : Γ.Nonempty)
    (k : Fin n → ℕ) :
    (∀ j γ, γ ∈ Γ → hullThresh Γ hΓ k j ≤ k (γ.symm j)) ∧
      (∀ j, ∃ γ ∈ Γ, hullThresh Γ hΓ k j = k (γ.symm j)) := by
  constructor
  · intro j γ hγ
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hγ)
  · intro j
    have hmem := Finset.min'_mem (Γ.image (fun γ => k (γ.symm j))) (hΓ.image _)
    rw [Finset.mem_image] at hmem
    obtain ⟨γ, hγ, hve⟩ := hmem
    exact ⟨γ, hγ, hve.symm⟩

/-- **M2.rectangular_hull_minimality.**  The hull box contains the orbit union,
and every coordinate box with thresholds bounded by `N` that contains the orbit
union contains the hull box.  Together with `hull_thresholds` this pins down the
hull thresholds exactly. -/
theorem hull_minimal {p N n : ℕ} (hp : p.Prime) (Γ : Finset (Equiv.Perm (Fin n)))
    (hΓ : Γ.Nonempty) (k : Fin n → ℕ) (hkN : ∀ j, k j ≤ N) :
    (∀ x, orbitUnion p N n Γ k x → Box p N n (hullThresh Γ hΓ k) x) ∧
      (∀ k' : Fin n → ℕ, (∀ j, k' j ≤ N) →
        (∀ x, orbitUnion p N n Γ k x → Box p N n k' x) →
          ∀ x, Box p N n (hullThresh Γ hΓ k) x → Box p N n k' x) := by
  have hhull := hull_thresholds Γ hΓ k
  constructor
  · rintro x ⟨γ, hγ, hγx⟩
    exact box_mono (fun j => hhull.1 j γ hγ) ((mem_permAct_box γ k x).mp hγx)
  · intro k' hk'N hU x hx
    refine box_mono (fun j => ?_) hx
    obtain ⟨γ, hγ, hval⟩ := hhull.2 j
    have hsub : Box p N n (fun i => k (γ.symm i)) ⊆ Box p N n k' := fun y hy =>
      hU y ⟨γ, hγ, (mem_permAct_box γ k y).mpr hy⟩
    have hle := le_of_box_subset hp (fun i => hkN (γ.symm i)) hk'N hsub j
    omega

/-! ## 4. Stage 2: exact cardinality and the integer enlargement budget -/

/-- The explicit bijection `B k ≃ ∏ j, Fin (p ^ (N - k j))`: a coordinate is
determined by `p ^ (k j) * d` with `0 ≤ d < p ^ (N - k j)`. -/
def boxFinEquiv (p N n : ℕ) (hp : p.Prime) (k : Fin n → ℕ) (hkN : ∀ j, k j ≤ N) :
    ↥(Box p N n k) ≃ ((j : Fin n) → Fin (p ^ (N - k j))) where
  toFun x j :=
    ⟨(x.1 j).val / p ^ (k j), by
      have : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
      have hpos : 0 < p ^ (k j) := pow_pos hp.pos _
      rw [Nat.div_lt_iff_lt_mul hpos]
      calc (x.1 j).val < p ^ N := ZMod.val_lt (x.1 j)
        _ = p ^ (N - k j) * p ^ (k j) := by rw [mul_comm, pow_mul_pow_sub (hkN j)]⟩
  invFun v :=
    ⟨fun j => ((p ^ (k j) * (v j).val : ℕ) : ZMod (p ^ N)), by
      intro j
      rw [ZMod.val_natCast]
      exact (Nat.dvd_mod_iff (pow_dvd_pow p (hkN j))).mpr (dvd_mul_right _ _)⟩
  left_inv x := by
    have : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
    ext j
    show ((p ^ (k j) * ((x.1 j).val / p ^ (k j)) : ℕ) : ZMod (p ^ N)) = x.1 j
    rw [mul_comm, Nat.div_mul_cancel (x.2 j)]
    exact ZMod.natCast_zmod_val (x.1 j)
  right_inv v := by
    funext j
    apply Fin.ext
    show (((p ^ (k j) * (v j).val : ℕ) : ZMod (p ^ N))).val / p ^ (k j) = (v j).val
    rw [ZMod.val_natCast]
    have hlt : p ^ (k j) * (v j).val < p ^ N := by
      have hv : (v j).val < p ^ (N - k j) := (v j).isLt
      calc p ^ (k j) * (v j).val < p ^ (k j) * p ^ (N - k j) :=
            Nat.mul_lt_mul_of_pos_left hv (pow_pos hp.pos _)
        _ = p ^ N := pow_mul_pow_sub (hkN j)
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mul_div_cancel_left (v j).val (pow_pos hp.pos _)

/-- **M2.box_cardinality.**  `Nat.card (B k) = p ^ ∑ j, (N - k j)`.

This is a finite cardinality, not a measure: see the module docstring. -/
theorem box_cardinality {p N n : ℕ} (hp : p.Prime) (k : Fin n → ℕ)
    (hkN : ∀ j, k j ≤ N) :
    Nat.card ↥(Box p N n k) = p ^ ∑ j, (N - k j) := by
  rw [Nat.card_congr (boxFinEquiv p N n hp k hkN), Nat.card_pi]
  simp only [Nat.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]

/-- **M2.enlargement_integer_budget.**  For `k' ≤ k` coordinatewise the
enlargement from `B k` to `B k'` is exactly the integer exponent
`∑ j, (k j - k' j)`:

`Nat.card (B k) * p ^ (∑ j, (k j - k' j)) = Nat.card (B k')`.

No real division and no `cost` function is introduced. -/
theorem enlargement_budget {p N n : ℕ} (hp : p.Prime) (k k' : Fin n → ℕ)
    (hkN : ∀ j, k j ≤ N) (hk'N : ∀ j, k' j ≤ N) (hle : ∀ j, k' j ≤ k j) :
    Nat.card ↥(Box p N n k) * p ^ (∑ j, (k j - k' j)) = Nat.card ↥(Box p N n k') := by
  rw [box_cardinality hp k hkN, box_cardinality hp k' hk'N, ← pow_add]
  have hsum : (∑ j, (N - k j)) + (∑ j, (k j - k' j)) = ∑ j, (N - k' j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by
      have h1 := hkN j
      have h2 := hle j
      omega)
  rw [hsum]

/-- The enlargement budget specialized to the hull of the orbit union: replacing
the original box by its rectangular hull costs exactly the integer exponent
`∑ j, (k j - hull j)`. -/
theorem enlargement_budget_hull {p N n : ℕ} (hp : p.Prime)
    (Γ : Finset (Equiv.Perm (Fin n))) (hΓ : Γ.Nonempty)
    (hid : (1 : Equiv.Perm (Fin n)) ∈ Γ) (k : Fin n → ℕ) (hkN : ∀ j, k j ≤ N) :
    Nat.card ↥(Box p N n k) * p ^ (∑ j, (k j - hullThresh Γ hΓ k j)) =
      Nat.card ↥(Box p N n (hullThresh Γ hΓ k)) := by
  have hhull := hull_thresholds Γ hΓ k
  have hle : ∀ j, hullThresh Γ hΓ k j ≤ k j := by
    intro j
    have h := hhull.1 j (1 : Equiv.Perm (Fin n)) hid
    have h1 : ((Equiv.symm (1 : Equiv.Perm (Fin n))) j) = j := rfl
    rwa [h1] at h
  have hbdd : ∀ j, hullThresh Γ hΓ k j ≤ N := fun j => (hle j).trans (hkN j)
  exact enlargement_budget hp k (hullThresh Γ hΓ k) hkN hbdd hle

/-! ## 5. Stage 3: the concrete `p = 2, N = 1, n = 2` check -/

/-- The threshold vector `(0, 1)` on two coordinates. -/
def kTwo : Fin 2 → ℕ := fun j => if j = 0 then 0 else 1

/-- The permutation family `{id, swap}` on two coordinates.  It is a finite
family, not assumed to be a group. -/
def gammaTwo : Finset (Equiv.Perm (Fin 2)) := {1, Equiv.swap 0 1}

lemma gammaTwo_nonempty : gammaTwo.Nonempty := ⟨1, by simp [gammaTwo]⟩

lemma gammaTwo_one_mem : (1 : Equiv.Perm (Fin 2)) ∈ gammaTwo := by simp [gammaTwo]

lemma gammaTwo_swap_mem : Equiv.swap 0 1 ∈ gammaTwo := by simp [gammaTwo]

lemma kTwo_zero : kTwo 0 = 0 := by simp [kTwo]

lemma kTwo_one : kTwo 1 = 1 := by simp [kTwo]

/-- Exhaustion of `Fin 2`, avoiding extra tactic imports. -/
lemma fin_two_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  have h : j.val < 2 := j.isLt
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · left
    exact Fin.ext (by simpa using h0)
  · right
    refine Fin.ext ?_
    have h1 : j.val = 1 := by omega
    simpa using h1

lemma zmod_two_two_dvd_iff (x : ZMod 2) : (2 ∣ x.val) ↔ x = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have hlt : x.val < 2 := ZMod.val_lt x
    have hc0 : c = 0 := by omega
    rw [hc0, Nat.mul_zero] at hc
    exact (ZMod.val_eq_zero x).mp hc
  · rintro rfl
    exact dvd_zero 2

lemma zmod_two_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hne : x.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero x).mp hv)
  have hv : x.val = 1 := by omega
  have h1 : (1 : ZMod 2).val = 1 := ZMod.val_one'' (by decide)
  exact ZMod.val_injective 2 (by rw [hv, h1])

lemma mem_box_kTwo (x : Fin 2 → ZMod (2 ^ 1)) : x ∈ Box 2 1 2 kTwo ↔ x 1 = 0 := by
  constructor
  · intro h
    have h' := h 1
    rw [kTwo_one] at h'
    exact (zmod_two_two_dvd_iff (x 1)).mp h'
  · intro h j
    rcases fin_two_cases j with rfl | rfl
    · rw [kTwo_zero]
      exact one_dvd _
    · rw [kTwo_one, h, ZMod.val_zero]
      exact dvd_zero 2

lemma mem_box_kTwo_swap (x : Fin 2 → ZMod (2 ^ 1)) :
    permAct 2 1 (Equiv.swap 0 1) x ∈ Box 2 1 2 kTwo ↔ x 0 = 0 := by
  rw [mem_box_kTwo]
  show x ((Equiv.swap 0 1) 1) = 0 ↔ x 0 = 0
  rw [Equiv.swap_apply_right]

/-- The orbit union for `Γ = {id, swap}` is the union of the two coordinate
half-spaces. -/
lemma orbitUnion_gammaTwo :
    orbitUnion 2 1 2 gammaTwo kTwo = {x : Fin 2 → ZMod (2 ^ 1) | x 0 = 0 ∨ x 1 = 0} := by
  ext x
  constructor
  · rintro ⟨γ, hγ, hγx⟩
    rcases Finset.mem_insert.mp hγ with rfl | hγ'
    · right
      have h' := hγx
      rw [mem_box_kTwo] at h'
      simpa [permAct] using h'
    · have hγs : γ = Equiv.swap 0 1 := Finset.mem_singleton.mp hγ'
      subst hγs
      left
      exact (mem_box_kTwo_swap x).mp hγx
  · rintro (h | h)
    · exact ⟨Equiv.swap 0 1, gammaTwo_swap_mem, (mem_box_kTwo_swap x).mpr h⟩
    · refine ⟨1, gammaTwo_one_mem, ?_⟩
      rw [mem_box_kTwo]
      simpa [permAct] using h

/-- The union of the two half-spaces is the complement of the single point
`(1,1)`. -/
lemma union_halfspaces_eq_ne :
    {x : Fin 2 → ZMod (2 ^ 1) | x 0 = 0 ∨ x 1 = 0} =
      {x : Fin 2 → ZMod (2 ^ 1) | x ≠ fun _ => 1} := by
  ext x
  constructor
  · rintro (h | h) hx
    · rw [hx] at h
      exact absurd h (by decide)
    · rw [hx] at h
      exact absurd h (by decide)
  · intro hx
    by_contra hcon
    have h0 : x 0 ≠ 0 := fun h => hcon (Or.inl h)
    have h1 : x 1 ≠ 0 := fun h => hcon (Or.inr h)
    have h0' : x 0 = 1 := zmod_two_eq_one_of_ne_zero h0
    have h1' : x 1 = 1 := zmod_two_eq_one_of_ne_zero h1
    apply hx
    funext j
    rcases fin_two_cases j with rfl | rfl
    · simpa using h0'
    · simpa using h1'

/-- The hull thresholds in the concrete example are all zero: the rectangular
hull of the two half-spaces is the whole plane. -/
lemma hullThresh_gammaTwo :
    hullThresh gammaTwo gammaTwo_nonempty kTwo = fun _ => 0 := by
  have hhull := hull_thresholds gammaTwo gammaTwo_nonempty kTwo
  funext j
  have hle : hullThresh gammaTwo gammaTwo_nonempty kTwo j ≤ 0 := by
    rcases fin_two_cases j with rfl | rfl
    · have h := hhull.1 0 (1 : Equiv.Perm (Fin 2)) gammaTwo_one_mem
      have h1 : ((Equiv.symm (1 : Equiv.Perm (Fin 2))) 0) = 0 := rfl
      rw [h1, kTwo_zero] at h
      exact h
    · have h := hhull.1 1 (Equiv.swap 0 1) gammaTwo_swap_mem
      have h1 : ((Equiv.symm (Equiv.swap (0 : Fin 2) 1)) (1 : Fin 2)) = 0 := by
        rw [Equiv.symm_swap, Equiv.swap_apply_right]
      rw [h1, kTwo_zero] at h
      exact h
  omega

/-- **M2.two_three_four_example.**  For `p = 2`, `N = 1`, `n = 2`, `k = (0,1)`
and `Γ = {id, swap}`: the box has `2` points, the orbit union has `3` points, and
the rectangular hull has `4` points.  These three distinct numbers are the point
of the example: the orbit union is *not* the rectangular hull. -/
theorem two_three_four :
    Nat.card ↥(Box 2 1 2 kTwo) = 2 ∧
      Nat.card ↥(orbitUnion 2 1 2 gammaTwo kTwo) = 3 ∧
        Nat.card ↥(Box 2 1 2 (hullThresh gammaTwo gammaTwo_nonempty kTwo)) = 4 := by
  have hkN : ∀ j : Fin 2, kTwo j ≤ 1 := by decide
  have hsum : (∑ j : Fin 2, (1 - kTwo j)) = 1 := by
    rw [Fin.sum_univ_two]
    simp [kTwo]
  refine ⟨?_, ?_, ?_⟩
  · rw [box_cardinality (p := 2) (N := 1) Nat.prime_two kTwo hkN, hsum]
    rfl
  · rw [orbitUnion_gammaTwo, union_halfspaces_eq_ne, Nat.card_eq_fintype_card,
      Set.card_ne_eq]
    have hcard : Fintype.card (Fin 2 → ZMod (2 ^ 1)) = 4 := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      decide
    rw [hcard]
  · rw [hullThresh_gammaTwo]
    have hsum0 : (∑ j : Fin 2, (1 - (fun _ => (0 : ℕ)) j)) = 2 := by
      rw [Fin.sum_univ_two]
      simp
    rw [box_cardinality (p := 2) (N := 1) Nat.prime_two (fun _ => 0)
      (fun j => by omega), hsum0]
    decide

end OrbitQuotient
