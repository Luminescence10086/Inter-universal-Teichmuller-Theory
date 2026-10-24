import ContinuousKummerTheory.Kummer.Equiv
import KummerValuationSeparation

/-! Actual continuous H1 Kummer classes, not an abstract class-equality field.
The kernel theorem supplies a power witness. Discrete valuation then separates
classes with an independent finite bound, or along an unbounded tower.
No reflection of an unproved inflation map is used. -/
set_option autoImplicit false
open scoped Pointwise

namespace CoreKummerClassValuationBridge
open KummerTheory CoreKummerValuationSeparation
noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsGalois ℚ_[p] Ω]

/-- The real Kummer kernel turns equality of H1 classes into an actual power ratio. -/
theorem power_ratio_of_kummer_eq (n : ℕ) [HasKummerRoots n ℚ_[p] Ω]
    (x y : ℚ_[p]ˣ) (h : kummer n ℚ_[p] Ω x = kummer n ℚ_[p] Ω y) :
    ∃ z : ℚ_[p], (x : ℚ_[p]) / (y : ℚ_[p]) = z ^ n := by
  have hker : x / y ∈ (kummer n ℚ_[p] Ω).ker := by
    rw [MonoidHom.mem_ker, map_div, h, div_self']
  rw [ker_kummer] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨(z : ℚ_[p]), ?_⟩
  simpa only [powMonoidHom_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    using (congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p])) hz).symm

theorem valuation_eq_of_kummer_eq_and_bound (n : ℕ)
    [HasKummerRoots n ℚ_[p] Ω] (x y : ℚ_[p]ˣ)
    (hbound : ((x : ℚ_[p]).valuation - (y : ℚ_[p]).valuation).natAbs < n)
    (h : kummer n ℚ_[p] Ω x = kummer n ℚ_[p] Ω y) :
    (x : ℚ_[p]).valuation = (y : ℚ_[p]).valuation :=
  valuation_eq_of_bounded_power x.ne_zero y.ne_zero n hbound
    (power_ratio_of_kummer_eq n x y h)

theorem principal_eq_of_kummer_eq_and_bound (n : ℕ)
    [HasKummerRoots n ℚ_[p] Ω] (x y : ℚ_[p]ˣ)
    (hbound : ((x : ℚ_[p]).valuation - (y : ℚ_[p]).valuation).natAbs < n)
    (h : kummer n ℚ_[p] Ω x = kummer n ℚ_[p] Ω y) :
    (x : ℚ_[p]) • integerRegion p = (y : ℚ_[p]) • integerRegion p :=
  principal_eq_of_bounded_power x.ne_zero y.ne_zero n hbound
    (power_ratio_of_kummer_eq n x y h)

/-- Common-field classes along an unbounded tower determine the principal lattice.
The root-existence instances are arithmetic extension data, not the conclusion. -/
theorem principal_eq_of_kummer_tower (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) ℚ_[p] Ω) (x y : ℚ_[p]ˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) ℚ_[p] Ω x = kummer (ell ^ k) ℚ_[p] Ω y) :
    (x : ℚ_[p]) • integerRegion p = (y : ℚ_[p]) • integerRegion p := by
  apply principal_eq_of_power_tower x.ne_zero y.ne_zero ell hell
  intro k
  let _ := roots k
  exact power_ratio_of_kummer_eq (ell ^ k) x y (h k)

/-- A normalized value which is itself an ell-th power is invisible at level ell.
It is unsafe to identify its level-ell class with that of the chosen root. -/
theorem level_power_is_trivial (n : ℕ) [HasKummerRoots n ℚ_[p] Ω]
    (b : ℚ_[p]ˣ) : kummer n ℚ_[p] Ω (b ^ n) = 1 := by
  rw [← MonoidHom.mem_ker, ker_kummer]
  exact ⟨b, rfl⟩

/-- Normalization by an m-th power can be cancelled on the level-n Kummer
image when m and n are coprime. At n = m this premise usually fails. -/
theorem kummer_eq_of_coprime_power_eq (m n : ℕ) (hcop : m.Coprime n)
    [HasKummerRoots n ℚ_[p] Ω] (x y : ℚ_[p]ˣ)
    (h : kummer n ℚ_[p] Ω (x ^ m) = kummer n ℚ_[p] Ω (y ^ m)) :
    kummer n ℚ_[p] Ω x = kummer n ℚ_[p] Ω y := by
  have hm : (kummer n ℚ_[p] Ω x / kummer n ℚ_[p] Ω y) ^ m = 1 := by
    rw [div_pow, ← map_pow, ← map_pow, h, div_self']
  have hn : (kummer n ℚ_[p] Ω x / kummer n ℚ_[p] Ω y) ^ n = 1 := by
    rw [div_pow, ← map_pow, ← map_pow,
      level_power_is_trivial n x, level_power_is_trivial n y, div_self']
  exact div_eq_one.mp ((pow_eq_one_iff_of_coprime hcop).mp ⟨hm, hn⟩)

/-- A precise consumer of a normalized power-class comparison: coprimality
removes the normalization power; a separate bound then separates the lattice. -/
theorem principal_eq_of_coprime_power_class_and_bound
    (m n : ℕ) (hcop : m.Coprime n) [HasKummerRoots n ℚ_[p] Ω]
    (x y : ℚ_[p]ˣ)
    (hbound : ((x : ℚ_[p]).valuation - (y : ℚ_[p]).valuation).natAbs < n)
    (h : kummer n ℚ_[p] Ω (x ^ m) = kummer n ℚ_[p] Ω (y ^ m)) :
    (x : ℚ_[p]) • integerRegion p = (y : ℚ_[p]) • integerRegion p :=
  principal_eq_of_kummer_eq_and_bound n x y hbound
    (kummer_eq_of_coprime_power_eq m n hcop x y h)

/-- Even when the normalization power is not coprime to the tower prime,
an entire unbounded tower of normalized classes still determines the lattice.
This recovers valuations, not a chosen root or an individual finite-level class. -/
theorem principal_eq_of_normalized_kummer_tower (m : ℕ) (hm : m ≠ 0)
    (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) ℚ_[p] Ω) (x y : ℚ_[p]ˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) ℚ_[p] Ω (x ^ m) = kummer (ell ^ k) ℚ_[p] Ω (y ^ m)) :
    (x : ℚ_[p]) • integerRegion p = (y : ℚ_[p]) • integerRegion p := by
  have hv : ((x : ℚ_[p]) ^ m).valuation = ((y : ℚ_[p]) ^ m).valuation := by
    apply valuation_eq_of_power_tower (pow_ne_zero m x.ne_zero)
      (pow_ne_zero m y.ne_zero) ell hell
    intro k
    let _ := roots k
    simpa only [Units.val_pow_eq_pow_val] using
      power_ratio_of_kummer_eq (ell ^ k) (x ^ m) (y ^ m) (h k)
  rw [Padic.valuation_pow, Padic.valuation_pow] at hv
  exact principal_eq_of_valuation_eq x.ne_zero y.ne_zero
    (mul_left_cancel₀ (by exact_mod_cast hm : (m : ℤ) ≠ 0) hv)

end
end CoreKummerClassValuationBridge

#print axioms KummerTheory.ker_kummer
#print axioms KummerTheory.kummerEquiv
#print axioms CoreKummerClassValuationBridge.power_ratio_of_kummer_eq
#print axioms CoreKummerClassValuationBridge.valuation_eq_of_kummer_eq_and_bound
#print axioms CoreKummerClassValuationBridge.principal_eq_of_kummer_eq_and_bound
#print axioms CoreKummerClassValuationBridge.principal_eq_of_kummer_tower
#print axioms CoreKummerClassValuationBridge.level_power_is_trivial
#print axioms CoreKummerClassValuationBridge.kummer_eq_of_coprime_power_eq
#print axioms CoreKummerClassValuationBridge.principal_eq_of_coprime_power_class_and_bound
#print axioms CoreKummerClassValuationBridge.principal_eq_of_normalized_kummer_tower
