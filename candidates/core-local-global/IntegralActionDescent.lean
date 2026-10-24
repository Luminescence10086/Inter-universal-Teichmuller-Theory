import LatticeStabilizer
import ResidueHaar

/-! A common finite quotient is constructed from actual integral lattice
automorphisms. The same quotient works for an arbitrary family, and a full
residue cylinder's saturation is exactly another cylinder. This controls the
additive lattice, not an unproved maximal-order hull or an IUT native output. -/
set_option autoImplicit false
open Set Matrix MeasureTheory
open scoped ENNReal

namespace CoreIntegralActionDescent
noncomputable section

section Equivariant
variable {X Y : Type*}

/-- A commuting square of actual bijections transports a full cylinder exactly.
No invariance of the starting cylinder is required. -/
theorem image_cylinder (q : X → Y) (e : X ≃ X) (d : Y ≃ Y)
    (hcomm : ∀ x, q (e x) = d (q x)) (s : Set Y) :
    e '' (q ⁻¹' s) = q ⁻¹' (d '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨q x, hx, (hcomm x).symm⟩
  · rintro ⟨a, ha, heq⟩
    have hx : q (e.symm y) = a := by
      apply d.injective
      rw [← hcomm, e.apply_symm_apply, heq]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change q (e.symm y) ∈ s
    rwa [hx]

theorem saturation_cylinder {T : Type*} (q : X → Y)
    (e : T → X ≃ X) (d : T → Y ≃ Y)
    (hcomm : ∀ t x, q (e t x) = d t (q x)) (s : Set Y) :
    (⋃ t, e t '' (q ⁻¹' s)) = q ⁻¹' (⋃ t, d t '' s) := by
  simp_rw [image_cylinder q _ _ (hcomm _) s]
  exact (Set.preimage_iUnion).symm
end Equivariant

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The vector bijection of an actual matrix unit, with its actual inverse. -/
def matrixEquiv {R : Type*} [CommRing R] (U : (Matrix n n R)ˣ) :
    (n → R) ≃ (n → R) where
  toFun := (U : Matrix n n R).mulVec
  invFun := (↑(U⁻¹) : Matrix n n R).mulVec
  left_inv x := by
    have hi : (↑(U⁻¹) : Matrix n n R) * (U : Matrix n n R) = 1 := U.inv_val
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  right_inv x := by
    have hi : (U : Matrix n n R) * (↑(U⁻¹) : Matrix n n R) = 1 := U.val_inv
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]

variable (p : ℕ) [Fact p.Prime]

/-- Reduction of the matrix and its inverse. No separate congruence hypothesis. -/
def reduceUnit (k : ℕ) (U : (Matrix n n ℤ_[p])ˣ) :
    (Matrix n n (ZMod (p ^ k)))ˣ :=
  Units.map (PadicInt.toZModPow (p := p) k).mapMatrix.toMonoidHom U

theorem reduction_commutes (k : ℕ) (U : (Matrix n n ℤ_[p])ˣ)
    (x : n → ℤ_[p]) :
    CoreResidueHaar.reduction p n k (matrixEquiv U x) =
      matrixEquiv (reduceUnit p k U) (CoreResidueHaar.reduction p n k x) := by
  ext i
  exact (PadicInt.toZModPow (p := p) k).map_mulVec (U : Matrix n n ℤ_[p]) x i

/-- Any family (even infinite) uses the same reduction map at each precision. -/
theorem integral_saturation_cylinder {T : Type*} (k : ℕ)
    (U : T → (Matrix n n ℤ_[p])ˣ) (s : Set (n → ZMod (p ^ k))) :
    (⋃ t, matrixEquiv (U t) '' (CoreResidueHaar.reduction p n k ⁻¹' s)) =
      CoreResidueHaar.reduction p n k ⁻¹'
        (⋃ t, matrixEquiv (reduceUnit p k (U t)) '' s) :=
  saturation_cylinder _ _ _ (fun t x => reduction_commutes p k (U t) x) s

/-- A finite carrier exists because the residue space is finite. For arbitrary
infinite T this is noncomputable: no enumeration algorithm for T is asserted. -/
def saturatedResidues {T : Type*} (k : ℕ)
    (U : T → (Matrix n n ℤ_[p])ˣ) (s : Set (n → ZMod (p ^ k))) :
    Finset (n → ZMod (p ^ k)) :=
  (Set.toFinite (⋃ t, matrixEquiv (reduceUnit p k (U t)) '' s)).toFinset

theorem coe_saturatedResidues {T : Type*} (k : ℕ)
    (U : T → (Matrix n n ℤ_[p])ˣ) (s : Set (n → ZMod (p ^ k))) :
    (saturatedResidues p k U s : Set (n → ZMod (p ^ k))) =
      ⋃ t, matrixEquiv (reduceUnit p k (U t)) '' s := by
  simp [saturatedResidues]

/-- Exact normalized Haar volume of the saturated cylinder. Individual
automorphisms preserve volume, but the union need not have the original volume. -/
theorem saturation_measure {T : Type*} (k : ℕ)
    (U : T → (Matrix n n ℤ_[p])ˣ) (s : Set (n → ZMod (p ^ k))) :
    CoreResidueHaar.latticeHaar p n
      (⋃ t, matrixEquiv (U t) '' (CoreResidueHaar.reduction p n k ⁻¹' s)) =
      ((saturatedResidues p k U s).card : ℝ≥0∞) /
        ((p ^ k) ^ Fintype.card n : ℕ) := by
  rw [integral_saturation_cylinder, ← coe_saturatedResidues]
  simpa [Fintype.card_fun] using CoreResidueHaar.cylinder_measure
    (CoreResidueHaar.latticeHaar p n)
    (CoreResidueHaar.reduction p n k).toAddMonoidHom
    (CoreResidueHaar.reduction_surjective p n k)
    (fun a => (CoreResidueHaar.reduction_continuous p n k).measurable
      (measurableSet_singleton a)) (saturatedResidues p k U s)

/-- Existing same-lattice stabilization supplies the integral action rather
than making integral inverse laws an additional premise. -/
def fromStabilizer (U : (Matrix n n ℚ_[p])ˣ)
    (h : CoreLatticeStabilizer.action U '' CoreLatticeStabilizer.standardLattice =
      CoreLatticeStabilizer.standardLattice) : (Matrix n n ℤ_[p])ˣ :=
  CoreLatticeStabilizer.integralStabilizer U h

theorem stabilizer_reduction_commutes (k : ℕ) (U : (Matrix n n ℚ_[p])ˣ)
    (h : CoreLatticeStabilizer.action U '' CoreLatticeStabilizer.standardLattice =
      CoreLatticeStabilizer.standardLattice) (x : n → ℤ_[p]) :
    CoreResidueHaar.reduction p n k (matrixEquiv (fromStabilizer p U h) x) =
      matrixEquiv (reduceUnit p k (fromStabilizer p U h))
        (CoreResidueHaar.reduction p n k x) :=
  reduction_commutes p k (fromStabilizer p U h) x

end
end CoreIntegralActionDescent

#print axioms CoreIntegralActionDescent.image_cylinder
#print axioms CoreIntegralActionDescent.saturation_cylinder
#print axioms CoreIntegralActionDescent.matrixEquiv
#print axioms CoreIntegralActionDescent.reduceUnit
#print axioms CoreIntegralActionDescent.reduction_commutes
#print axioms CoreIntegralActionDescent.integral_saturation_cylinder
#print axioms CoreIntegralActionDescent.saturatedResidues
#print axioms CoreIntegralActionDescent.coe_saturatedResidues
#print axioms CoreIntegralActionDescent.saturation_measure
#print axioms CoreIntegralActionDescent.fromStabilizer
#print axioms CoreIntegralActionDescent.stabilizer_reduction_commutes
