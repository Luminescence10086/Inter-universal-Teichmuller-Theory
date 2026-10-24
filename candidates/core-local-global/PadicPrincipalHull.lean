import PrincipalProduct
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Principal nonvanishing lattice containers in an actual product Q_p^n.
The coefficient ring is the genuine product Z_p^n. No original IUT coefficient
ring or native q-object is identified by this model. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace CorePadicPrincipalHull
noncomputable section
variable (p : ℕ) [Fact p.Prime] (ι : Type*)

abbrev Integral := ι → ℤ_[p]
abbrev Ambient := ι → ℚ_[p]

instance padicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
instance padicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The actual coordinate inclusion, retaining multiplication. -/
def embed : Integral p ι →+* Ambient p ι where
  toFun x i := x i
  map_one' := by ext i; exact map_one PadicInt.Coe.ringHom
  map_mul' x y := by ext i; exact map_mul PadicInt.Coe.ringHom (x i) (y i)
  map_zero' := by ext i; exact map_zero PadicInt.Coe.ringHom
  map_add' x y := by ext i; exact map_add PadicInt.Coe.ringHom (x i) (y i)

def embedLinear : Integral p ι →ₗ[Integral p ι] Ambient p ι where
  toFun := embed p ι
  map_add' := (embed p ι).map_add
  map_smul' r x := by
    ext i
    change PadicInt.Coe.ringHom (r i * x i) =
      PadicInt.Coe.ringHom (r i) * PadicInt.Coe.ringHom (x i)
    exact map_mul PadicInt.Coe.ringHom (r i) (x i)

/-- Multiplication by an ambient element, as a map from the stated coefficient
ring. Its range is precisely the lambda O lattice shape. -/
def principalMap (a : Ambient p ι) : Integral p ι →ₗ[Integral p ι] Ambient p ι where
  toFun x := a * embed p ι x
  map_add' x y := by rw [map_add, mul_add]
  map_smul' r x := by
    ext i
    change a i * PadicInt.Coe.ringHom (r i * x i) =
      PadicInt.Coe.ringHom (r i) * (a i * PadicInt.Coe.ringHom (x i))
    rw [map_mul]
    exact mul_left_comm _ _ _

def principalLattice (a : Ambient p ι) : Submodule (Integral p ι) (Ambient p ι) :=
  (principalMap p ι a).range

theorem mem_principalLattice (a y : Ambient p ι) :
    y ∈ principalLattice p ι a ↔ ∃ x : Integral p ι, a * embed p ι x = y := Iff.rfl

variable [Fintype ι]

/-- Every ideal in the finite product coefficient ring has the actual ambient
principal-lattice shape; component nonvanishing is established separately. -/
theorem image_ideal_generator (I : Ideal (Integral p ι)) :
    embed p ι '' (I : Set (Integral p ι)) =
      (principalLattice p ι (embed p ι (CorePrincipalProduct.generator I)) : Set (Ambient p ι)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hx
    apply (mem_principalLattice p ι _ _).mpr
    exact ⟨b, by rw [hb, map_mul]; rfl⟩
  · intro hy
    obtain ⟨b, hb⟩ := (mem_principalLattice p ι _ _).mp hy
    refine ⟨CorePrincipalProduct.generator I * b, I.mul_mem_right b ?_, ?_⟩
    · exact Submodule.IsPrincipal.generator_mem I
    · rw [map_mul]
      exact hb

/-- The kernel witness has nonzero components for every precision, including k=0. -/
def uniformWitness (k : ℕ) : Integral p ι := fun _ => (p : ℤ_[p]) ^ k

omit [Fintype ι] in
theorem uniformWitness_ne_zero (k : ℕ) : ∀ i, uniformWitness p ι k i ≠ 0 := by
  intro i
  exact pow_ne_zero k (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

omit [Fintype ι] in
/-- Finite residue ideals pull back to full-coordinate ideals automatically;
nonvanishing need not be assumed or deduced from an unproved volume formula. -/
theorem uniformWitness_mem_comap (k : ℕ) (J : Ideal (ι → ZMod (p ^ k))) :
    uniformWitness p ι k ∈ Ideal.comap (CoreResidueHaar.reduction p ι k) J := by
  have hzero : PadicInt.toZModPow (p := p) k ((p : ℤ_[p]) ^ k) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact Ideal.subset_span (by simp)
  change CoreResidueHaar.reduction p ι k (uniformWitness p ι k) ∈ J
  have heq : CoreResidueHaar.reduction p ι k (uniformWitness p ι k) = 0 := by
    ext i
    exact hzero
  rw [heq]
  exact J.zero_mem

theorem residue_container_principal (k : ℕ) (J : Ideal (ι → ZMod (p ^ k))) :
    ∃ a : Ambient p ι, (∀ i, a i ≠ 0) ∧
      embed p ι '' (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι)) =
        (principalLattice p ι a : Set (Ambient p ι)) := by
  let I := Ideal.comap (CoreResidueHaar.reduction p ι k) J
  have hne := CorePrincipalProduct.generator_components_ne_zero I (uniformWitness p ι k)
    (uniformWitness_mem_comap p ι k J) (uniformWitness_ne_zero p ι k)
  refine ⟨embed p ι (CorePrincipalProduct.generator I), ?_, image_ideal_generator p ι I⟩
  intro i hi
  apply hne i
  exact Subtype.ext hi

omit [Fintype ι] in
/-- Minimality among ALL ambient principal lattices, even fractional ones.
This is stronger than minimality among ideals contained in the integral region. -/
theorem span_image_minimal (A : Set (Integral p ι)) (a : Ambient p ι)
    (hA : embed p ι '' A ⊆ (principalLattice p ι a : Set (Ambient p ι))) :
    embed p ι '' (Ideal.span A : Set (Integral p ι)) ⊆
      (principalLattice p ι a : Set (Ambient p ι)) := by
  let J : Ideal (Integral p ι) := {
    carrier := {x | embed p ι x ∈ principalLattice p ι a}
    zero_mem' := by
      change embed p ι 0 ∈ principalLattice p ι a
      rw [map_zero]
      exact Submodule.zero_mem _
    add_mem' := by
      intro x y hx hy
      change embed p ι (x + y) ∈ principalLattice p ι a
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    smul_mem' := by
      intro r x hx
      change embed p ι (r * x) ∈ principalLattice p ι a
      have heq : embed p ι (r * x) = r • embed p ι x :=
        (embedLinear p ι).map_smul r x
      rw [heq]
      exact Submodule.smul_mem _ r hx }
  have hle : Ideal.span A ≤ J := Ideal.span_le.mpr (by
    intro x hx
    exact hA ⟨x, hx, rfl⟩)
  rintro y ⟨x, hx, rfl⟩
  exact hle hx

theorem embed_openEmbedding : Topology.IsOpenEmbedding (embed p ι) :=
  Topology.IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe

/-- The integral region as a positive compact subset of the actual ambient
noncompact vector space, used to normalize its Haar measure. -/
def integralCompact : TopologicalSpace.PositiveCompacts (Ambient p ι) :=
  (⊤ : TopologicalSpace.PositiveCompacts (Integral p ι)).map (embed p ι)
    (embed_openEmbedding p ι).continuous (embed_openEmbedding p ι).isOpenMap

theorem coe_integralCompact :
    (integralCompact p ι : Set (Ambient p ι)) = embed p ι '' Set.univ := rfl

def ambientHaar : Measure (Ambient p ι) := Measure.addHaarMeasure (integralCompact p ι)

instance ambientHaar_isHaar : (ambientHaar p ι).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure (integralCompact p ι)).IsAddHaarMeasure

theorem ambientHaar_integral :
    ambientHaar p ι (embed p ι '' Set.univ) = 1 :=
  Measure.addHaarMeasure_self (K₀ := integralCompact p ι)

def pulledHaar : Measure (Integral p ι) := (ambientHaar p ι).comap (embed p ι)

instance pulledHaar_isHaar : (pulledHaar p ι).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.comap (ambientHaar p ι)
    (mH := inferInstance) (f := (embed p ι).toAddMonoidHom) (embed_openEmbedding p ι)

instance pulledHaar_probability : IsProbabilityMeasure (pulledHaar p ι) where
  measure_univ := by
    change ((ambientHaar p ι).comap (embed p ι)) Set.univ = 1
    rw [Measure.comap_apply (embed p ι) (embed_openEmbedding p ι).injective
      (fun s hs => (embed_openEmbedding p ι).measurableEmbedding.measurableSet_image.mpr hs)
      (ambientHaar p ι) MeasurableSet.univ]
    exact ambientHaar_integral p ι

/-- The previous compact-lattice normalization is the pullback of genuine
ambient Haar measure. It is not mistaken for a probability measure on Q_p^n. -/
theorem pulledHaar_eq : pulledHaar p ι = CoreResidueHaar.latticeHaar p ι :=
  Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem ambient_image_measure (A : Set (Integral p ι)) (hA : MeasurableSet A) :
    ambientHaar p ι (embed p ι '' A) = CoreResidueHaar.latticeHaar p ι A := by
  rw [← pulledHaar_eq p ι]
  exact (Measure.comap_apply (embed p ι) (embed_openEmbedding p ι).injective
    (fun s hs => (embed_openEmbedding p ι).measurableEmbedding.measurableSet_image.mpr hs)
    (ambientHaar p ι) hA).symm

theorem residue_container_volume [DecidableEq ι] (k : ℕ) (J : Ideal (ι → ZMod (p ^ k))) :
    ambientHaar p ι
      (embed p ι '' (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι))) =
      ((CoreResidueHull.idealResidues J).card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  classical
  have heq : (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι)) =
      CoreResidueHaar.reduction p ι k ⁻¹' (CoreResidueHull.idealResidues J : Set _) := by
    rw [CoreResidueHull.coe_idealResidues]
    rfl
  have hmeas : MeasurableSet
      (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι)) := by
    rw [heq]
    exact (CoreResidueHaar.reduction_continuous p ι k).measurable
      (CoreResidueHull.idealResidues J).measurableSet
  rw [ambient_image_measure p ι _ hmeas, heq]
  exact CoreResidueHaar.residue_cylinder_measure p ι k (CoreResidueHull.idealResidues J)

theorem principalLattice_compact (a : Ambient p ι) :
    IsCompact (principalLattice p ι a : Set (Ambient p ι)) := by
  have heq : (principalLattice p ι a : Set (Ambient p ι)) =
      (fun x : Integral p ι => a * embed p ι x) '' Set.univ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (mem_principalLattice p ι a y).mp hy
      exact ⟨x, Set.mem_univ x, hx⟩
    · rintro ⟨x, _, hx⟩
      exact (mem_principalLattice p ι a y).mpr ⟨x, hx⟩
  rw [heq]
  exact isCompact_univ.image (continuous_const.mul (embed_openEmbedding p ι).continuous)

theorem residue_container_positive (k : ℕ) (J : Ideal (ι → ZMod (p ^ k))) :
    0 < ambientHaar p ι
      (embed p ι '' (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι))) := by
  classical
  rw [residue_container_volume p ι k J]
  apply ENNReal.div_pos
  · have hcard : (CoreResidueHull.idealResidues J).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨0, by simp [CoreResidueHull.idealResidues]⟩
    exact_mod_cast hcard
  · exact ENNReal.natCast_ne_top _

/-- A finite ideal certificate gives a nonvanishing, compact principal lattice
in Q_p^n with an exact AMBIENT Haar volume. -/
theorem principal_container_certificate [DecidableEq ι] (k : ℕ)
    (J : Ideal (ι → ZMod (p ^ k))) :
    ∃ a : Ambient p ι, (∀ i, a i ≠ 0) ∧
      embed p ι '' (Ideal.comap (CoreResidueHaar.reduction p ι k) J : Set (Integral p ι)) =
        (principalLattice p ι a : Set (Ambient p ι)) ∧
      ambientHaar p ι (principalLattice p ι a : Set (Ambient p ι)) =
        ((CoreResidueHull.idealResidues J).card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  obtain ⟨a, hane, hshape⟩ := residue_container_principal p ι k J
  refine ⟨a, hane, hshape, ?_⟩
  rw [← hshape]
  exact residue_container_volume p ι k J

/-- Every covered region obtains a genuine nonvanishing principal container.
This does not assume that its own arbitrary module span is the holomorphic hull. -/
theorem principal_container_of_cover [DecidableEq ι] (k : ℕ)
    (J : Ideal (ι → ZMod (p ^ k))) (A : Set (Integral p ι))
    (hcover : ∀ x ∈ A, CoreResidueHaar.reduction p ι k x ∈ J) :
    ∃ a : Ambient p ι, (∀ i, a i ≠ 0) ∧
      embed p ι '' A ⊆ (principalLattice p ι a : Set (Ambient p ι)) ∧
      ambientHaar p ι (principalLattice p ι a : Set (Ambient p ι)) =
        ((CoreResidueHull.idealResidues J).card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  obtain ⟨a, hane, hshape, hvol⟩ := principal_container_certificate p ι k J
  refine ⟨a, hane, ?_, hvol⟩
  rw [← hshape]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hcover x hx, rfl⟩

/-- The certificate covers an entire possibly infinite allowed family in one
principal lattice, through a common finite quotient and common ideal. -/
theorem saturation_principal_container [DecidableEq ι] {T : Type*} (k : ℕ)
    (J : Ideal (ι → ZMod (p ^ k))) (A : Set (Integral p ι))
    (s : Set (ι → ZMod (p ^ k))) (u : T → Integral p ι → Integral p ι)
    (v : T → (ι → ZMod (p ^ k)) → (ι → ZMod (p ^ k)))
    (hcomm : ∀ i x, CoreResidueHaar.reduction p ι k (u i x) =
      v i (CoreResidueHaar.reduction p ι k x))
    (hA : ∀ x ∈ A, CoreResidueHaar.reduction p ι k x ∈ s)
    (hcover : ∀ i x, x ∈ s → v i x ∈ J) :
    ∃ a : Ambient p ι, (∀ i, a i ≠ 0) ∧
      embed p ι '' (⋃ i, u i '' A) ⊆ (principalLattice p ι a : Set (Ambient p ι)) ∧
      ambientHaar p ι (principalLattice p ι a : Set (Ambient p ι)) =
        ((CoreResidueHull.idealResidues J).card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  apply principal_container_of_cover p ι k J (⋃ i, u i '' A)
  intro y hy
  obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
  rw [hcomm]
  exact hcover i _ (hA x hx)

/-- A hull characterized by minimality among nonvanishing lambda O lattices
inherits the certified bound. The premise is geometric minimality, not the
desired numerical inequality or an identification with arbitrary module span. -/
theorem minimal_hull_volume_le [DecidableEq ι] (k : ℕ)
    (J : Ideal (ι → ZMod (p ^ k))) (A : Set (Integral p ι))
    (hcover : ∀ x ∈ A, CoreResidueHaar.reduction p ι k x ∈ J)
    (H : Set (Ambient p ι))
    (hminimal : ∀ a : Ambient p ι, (∀ i, a i ≠ 0) →
      embed p ι '' A ⊆ (principalLattice p ι a : Set (Ambient p ι)) →
      H ⊆ (principalLattice p ι a : Set (Ambient p ι))) :
    ambientHaar p ι H ≤
      ((CoreResidueHull.idealResidues J).card : ℝ≥0∞) / ((p ^ k) ^ Fintype.card ι : ℕ) := by
  obtain ⟨a, hane, hA, hvol⟩ := principal_container_of_cover p ι k J A hcover
  calc
    ambientHaar p ι H ≤ ambientHaar p ι (principalLattice p ι a : Set (Ambient p ι)) :=
      measure_mono (hminimal a hane hA)
    _ = _ := hvol

set_option maxHeartbeats 800000 in
/-- For a nonempty full residue cylinder its actual ideal hull is a least
nonvanishing principal lattice, even among ambient fractional principal lattices. -/
theorem cylinder_least_principal (k : ℕ) (s : Finset (ι → ZMod (p ^ k)))
    (hne : s.Nonempty) :
    ∃ a : Ambient p ι, (∀ i, a i ≠ 0) ∧
      embed p ι '' (CoreResidueHaar.reduction p ι k ⁻¹' (s : Set (ι → ZMod (p ^ k)))) ⊆
        (principalLattice p ι a : Set (Ambient p ι)) ∧
      ∀ b : Ambient p ι,
        embed p ι '' (CoreResidueHaar.reduction p ι k ⁻¹' (s : Set (ι → ZMod (p ^ k)))) ⊆
          (principalLattice p ι b : Set (Ambient p ι)) →
        (principalLattice p ι a : Set (Ambient p ι)) ⊆
          (principalLattice p ι b : Set (Ambient p ι)) := by
  let I : Ideal (Integral p ι) := Ideal.comap (CoreResidueHaar.reduction p ι k)
    (Ideal.span (s : Set (ι → ZMod (p ^ k))))
  obtain ⟨a, hane, hshape⟩ := residue_container_principal p ι k
    (Ideal.span (s : Set (ι → ZMod (p ^ k))))
  have hI : I = Ideal.span
      (CoreResidueHaar.reduction p ι k ⁻¹' (s : Set (ι → ZMod (p ^ k)))) :=
    (CoreResidueHull.span_cylinder_eq (CoreResidueHaar.reduction p ι k)
      (CoreResidueHaar.reduction_surjective p ι k) (s : Set (ι → ZMod (p ^ k))) hne.to_set).symm
  change embed p ι '' (I : Set (Integral p ι)) = _ at hshape
  refine ⟨a, hane, ?_, ?_⟩
  · rw [← hshape, hI]
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, Ideal.subset_span hx, rfl⟩
  · intro b hb
    rw [← hshape, hI]
    exact span_image_minimal p ι _ b hb

end
end CorePadicPrincipalHull

#print axioms CorePadicPrincipalHull.mem_principalLattice
#print axioms CorePadicPrincipalHull.image_ideal_generator
#print axioms CorePadicPrincipalHull.uniformWitness_ne_zero
#print axioms CorePadicPrincipalHull.uniformWitness_mem_comap
#print axioms CorePadicPrincipalHull.residue_container_principal
#print axioms CorePadicPrincipalHull.span_image_minimal
#print axioms CorePadicPrincipalHull.embed_openEmbedding
#print axioms CorePadicPrincipalHull.coe_integralCompact
#print axioms CorePadicPrincipalHull.ambientHaar_integral
#print axioms CorePadicPrincipalHull.pulledHaar_eq
#print axioms CorePadicPrincipalHull.ambient_image_measure
#print axioms CorePadicPrincipalHull.residue_container_volume
#print axioms CorePadicPrincipalHull.principalLattice_compact
#print axioms CorePadicPrincipalHull.residue_container_positive
#print axioms CorePadicPrincipalHull.principal_container_certificate
#print axioms CorePadicPrincipalHull.principal_container_of_cover
#print axioms CorePadicPrincipalHull.saturation_principal_container
#print axioms CorePadicPrincipalHull.minimal_hull_volume_le
#print axioms CorePadicPrincipalHull.cylinder_least_principal
