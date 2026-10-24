import ResidueHaar
import SaturationGrowth

/-! A genuine Z_3^2 Haar-volume regression for orbit saturation and a larger
coordinate-ring ideal hull. Neither the ring nor its actions are claimed to be
an IUT object. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace CorePadicSaturation

/-- A commuting square of bijections transports an entire residue cylinder.
This is an equality of actual subsets, not just an equality of cardinalities. -/
theorem image_cylinder {G F : Type*} (q : G → F) (u : G ≃ G) (v : F ≃ F)
    (hcomm : ∀ x, q (u x) = v (q x)) (s : Set F) :
    u '' (q ⁻¹' s) = q ⁻¹' (v '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨q x, hx, (hcomm x).symm⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨u.symm y, ?_, u.apply_symm_apply y⟩
    have heq : v (q (u.symm y)) = v a := by
      rw [← hcomm, u.apply_symm_apply, hay]
    change q (u.symm y) ∈ s
    rw [v.injective heq]
    exact ha

noncomputable section
abbrev Lattice := Fin 2 → ℤ_[3]
abbrev Residue := CoreSaturationGrowth.Vec
abbrev μ : Measure Lattice := CoreResidueHaar.latticeHaar 3 (Fin 2)
abbrev q : Lattice →+* Residue := CoreResidueHaar.reduction 3 (Fin 2) 1

def cylinder (s : Finset Residue) : Set Lattice := q ⁻¹' (s : Set Residue)
def A : Set Lattice := cylinder CoreSaturationGrowth.region

def shear : Lattice ≃+ Lattice where
  toFun x := ![x 0 + x 1, x 1]
  invFun y := ![y 0 - y 1, y 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv y := by ext i; fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i
    · change (x 0 + y 0) + (x 1 + y 1) = (x 0 + x 1) + (y 0 + y 1)
      abel
    · rfl

def residueShear : Residue ≃ Residue :=
  Equiv.ofBijective CoreSaturationGrowth.shear.mulVec CoreSaturationGrowth.shear_bijective

theorem reduction_shear (x : Lattice) : q (shear x) = residueShear (q x) := by
  ext i
  fin_cases i <;>
    simp [q, CoreResidueHaar.reduction, shear, residueShear,
      CoreSaturationGrowth.shear, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem shear_continuous : Continuous shear := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (continuous_apply 0).add (continuous_apply 1)
  · exact continuous_apply 1

theorem shear_measurePreserving : MeasurePreserving shear μ μ :=
  shear.toAddMonoidHom.measurePreserving shear_continuous shear.surjective rfl

/-- The corresponding matrix has determinant one over Q_3. -/
theorem shear_det_one :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ_[3]).det = 1 := by
  norm_num [Matrix.det_fin_two]

theorem shear_image_cylinder (s : Finset Residue) :
    shear '' cylinder s = cylinder (s.image residueShear) := by
  simpa only [cylinder, Finset.coe_image, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv] using
    image_cylinder q shear.toEquiv residueShear reduction_shear (s : Set Residue)

theorem shear_image_A : shear '' A = cylinder CoreSaturationGrowth.moved :=
  shear_image_cylinder CoreSaturationGrowth.region

theorem cylinder_volume (s : Finset Residue) : μ (cylinder s) = (s.card : ℝ≥0∞) / 9 := by
  simpa [cylinder] using CoreResidueHaar.residue_cylinder_measure 3 (Fin 2) 1 s

theorem original_volume : μ A = 1 / 3 := by
  rw [A, cylinder_volume, CoreSaturationGrowth.region_card]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by norm_num))
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]

theorem moved_volume : μ (shear '' A) = 1 / 3 := by
  rw [shear_image_A, cylinder_volume, CoreSaturationGrowth.moved_card]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by norm_num))
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]

theorem saturated_volume : μ (A ∪ shear '' A) = 5 / 9 := by
  rw [shear_image_A]
  have hu : A ∪ cylinder CoreSaturationGrowth.moved =
      cylinder (CoreSaturationGrowth.region ∪ CoreSaturationGrowth.moved) := by
    ext x
    simp [A, cylinder]
  rw [hu, cylinder_volume, CoreSaturationGrowth.saturated_card]
  rfl

def coordinateIdeal : Ideal Lattice :=
  Ideal.comap q CoreSaturationGrowth.coordinateIdeal

theorem original_is_ideal : (coordinateIdeal : Set Lattice) = A := by
  ext x
  simp [coordinateIdeal, A, cylinder, CoreSaturationGrowth.region,
    CoreSaturationGrowth.coordinateIdeal]

theorem original_hull : Ideal.span A = coordinateIdeal := by
  rw [← original_is_ideal, Ideal.span_eq]

theorem one_mem_moved : (1 : Lattice) ∈ shear '' A := by
  rw [shear_image_A]
  change q 1 ∈ CoreSaturationGrowth.moved
  rw [map_one]
  exact CoreSaturationGrowth.one_mem_moved

/-- The hull is in the larger coordinatewise coefficient ring Z_3 × Z_3. -/
theorem moved_hull_top : Ideal.span (shear '' A) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span one_mem_moved)

theorem hull_volume : μ (Ideal.span (shear '' A) : Set Lattice) = 1 := by
  rw [moved_hull_top]
  exact measure_univ

theorem strict_saturation_growth : μ A < μ (A ∪ shear '' A) := by
  rw [original_volume, saturated_volume]
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by simp) (by norm_num))
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]

theorem hull_log_gain :
    Real.log (μ.real (Ideal.span (shear '' A) : Set Lattice)) - Real.log (μ.real A) =
      Real.log 3 := by
  simp only [Measure.real, hull_volume, original_volume, ENNReal.toReal_one,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.log_one, zero_sub]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

end
end CorePadicSaturation

#print axioms CorePadicSaturation.image_cylinder
#print axioms CorePadicSaturation.reduction_shear
#print axioms CorePadicSaturation.shear_continuous
#print axioms CorePadicSaturation.shear_measurePreserving
#print axioms CorePadicSaturation.shear_det_one
#print axioms CorePadicSaturation.shear_image_cylinder
#print axioms CorePadicSaturation.shear_image_A
#print axioms CorePadicSaturation.cylinder_volume
#print axioms CorePadicSaturation.original_volume
#print axioms CorePadicSaturation.moved_volume
#print axioms CorePadicSaturation.saturated_volume
#print axioms CorePadicSaturation.original_is_ideal
#print axioms CorePadicSaturation.original_hull
#print axioms CorePadicSaturation.one_mem_moved
#print axioms CorePadicSaturation.moved_hull_top
#print axioms CorePadicSaturation.hull_volume
#print axioms CorePadicSaturation.strict_saturation_growth
#print axioms CorePadicSaturation.hull_log_gain
