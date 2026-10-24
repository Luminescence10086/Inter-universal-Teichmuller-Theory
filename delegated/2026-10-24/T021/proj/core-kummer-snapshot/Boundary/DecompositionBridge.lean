import ContinuousKummerTheory.Kummer.DecompositionSurjective
import Boundary.ReducedComparison
import Boundary.PrecisionLoss

/-! A rational-point decomposition comparison, instantiated on the actual
restriction, coefficient reduction and residue Kummer maps. Source comparison
is still an explicit obligation; reduceMu is never assumed invertible. -/
set_option autoImplicit false

namespace CoreDecompositionBridge
open IsLocalRing KummerTheory KummerTheory.Decomposition
open scoped WithZero Pointwise

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ =
    algebraMap k (ResidueField A) c)
  [IsGalois F Ω] [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  (hres : ∀ (a : F) (ha : algebraMap F Ω a ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)

noncomputable def reducedClass (n : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]
    (f : Fˣ) : letI := muAction F A hk hkres n
      ContH1 (A.decompositionSubgroup F) (Mu n (ResidueField A)) :=
  let _ := muAction F A hk hkres n
  ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
    (reduceMu A n hn) continuous_of_discreteTopology
    (reduceMu_smul F A hk hkres n hn) (kummer n F Ω f)

include hres in
/-- Equality of reduced restrictions recovers residue-side Kummer classes at a
rational point. It does not recover the unreduced source classes. -/
theorem residue_kummer_eq_of_reduced_restrictions_eq
    (n : ℕ) (hn : n ≠ 0) [HasKummerRoots n F Ω]
    [HasKummerRoots n k (ResidueField A)]
    (f g : Fˣ) (a b : kˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hg : algebraMap F Ω g ∈ A) (hg' : algebraMap F Ω ↑g⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) a)
    (hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) b)
    (hcompare : reducedClass A hk hkres n hn f = reducedClass A hk hkres n hn g) :
    kummer n k (ResidueField A) a = kummer n k (ResidueField A) b := by
  let _ := muAction F A hk hkres n
  apply CoreReducedComparison.pullback_injective (decompositionMap F A hk hkres)
    (continuous_decompositionMap F A hk hkres)
    (decompositionMap_surjective (F := F) A hk hkres hres) (fun _ _ => rfl)
  exact (decomposition_kummer F A hk hkres n hn f a hf hf' hfa).symm.trans
    (hcompare.trans (decomposition_kummer F A hk hkres n hn g b hg hg' hgb))

variable [IsGalois k (ResidueField A)]

include hres in
/-- A finite comparison one normalization-factor higher determines the actual
principal valuation-ring lattice, with an independent bound on the exponents. -/
theorem principal_eq_of_reduced_comparison_and_bound
    (v : Valuation k ℤᵐ⁰) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    [HasKummerRoots (m * n) F Ω] [HasKummerRoots (m * n) k (ResidueField A)]
    (f g : Fˣ) (a b : kˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A)
    (hg : algebraMap F Ω g ∈ A) (hg' : algebraMap F Ω ↑g⁻¹ ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) (a ^ m))
    (hgb : residue A ⟨_, hg⟩ = algebraMap k (ResidueField A) (b ^ m))
    (hbound : (CoreDiscreteKummer.exponent v (a : k) -
      CoreDiscreteKummer.exponent v (b : k)).natAbs < n)
    (hcompare : reducedClass A hk hkres (m * n) (Nat.mul_ne_zero hm hn) f =
      reducedClass A hk hkres (m * n) (Nat.mul_ne_zero hm hn) g) :
    (a : k) • CoreDiscreteKummer.integerRegion v =
      (b : k) • CoreDiscreteKummer.integerRegion v := by
  apply CoreKummerPrecision.principal_eq_of_raised_level_and_bound
    (Ω := ResidueField A) v m n hm a b hbound
  exact residue_kummer_eq_of_reduced_restrictions_eq A hk hkres hres
    (m * n) (Nat.mul_ne_zero hm hn) f g (a ^ m) (b ^ m) hf hf' hg hg' hfa hgb hcompare

end CoreDecompositionBridge

#print axioms KummerTheory.Decomposition.decompositionMap_surjective
#print axioms CoreDecompositionBridge.reducedClass
#print axioms CoreDecompositionBridge.residue_kummer_eq_of_reduced_restrictions_eq
#print axioms CoreDecompositionBridge.principal_eq_of_reduced_comparison_and_bound
