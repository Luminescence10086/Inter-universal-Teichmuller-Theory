import IntegralActionDescent

/-!
# Actual frame coordinates for a lattice stabilizer

The integral action constructed from a stabilizer is the original p-adic action
on the actual frame lattice after the coordinate embedding. These statements
concern an additive lattice, without any claim about a multiplicative hull.
-/
set_option autoImplicit false

namespace CoreIntegralActionFrame

open Matrix CoreLatticeStabilizer CoreIntegralActionDescent

noncomputable section

variable {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]

/-- Coordinatewise embedding of p-adic integers into the ambient vector space. -/
def embed (x : n → ℤ_[p]) : n → ℚ_[p] := fun i => (x i : ℚ_[p])

omit [Fintype n] [DecidableEq n] in
theorem range_embed : Set.range (embed (p := p) (n := n)) = standardLattice := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ i
    exact (x i).property
  · intro hy
    exact ⟨fun i => ⟨y i, hy i⟩, rfl⟩

omit [Fintype n] [DecidableEq n] in
theorem embed_injective : Function.Injective (embed (p := p) (n := n)) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

/-- The actual embedding determined by the chosen full frame. -/
def frameEmbed (B : (Matrix n n ℚ_[p])ˣ) (x : n → ℤ_[p]) : n → ℚ_[p] :=
  action B (embed x)

theorem range_frameEmbed (B : (Matrix n n ℚ_[p])ˣ) :
    Set.range (frameEmbed B) = frameLattice B := by
  rw [frameLattice, ← range_embed, ← Set.range_comp]
  rfl

theorem frameEmbed_injective (B : (Matrix n n ℚ_[p])ˣ) :
    Function.Injective (frameEmbed B) :=
  (matrixEquiv B).injective.comp embed_injective

/-- The integral matrix action obtained by expressing the actual stabilizer in B. -/
def frameIntegral (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) : (Matrix n n ℤ_[p])ˣ :=
  fromStabilizer p (B⁻¹ * U * B) (conjugate_stabilizes_standard U B h)

theorem embed_fromStabilizer (U : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' standardLattice = standardLattice) (x : n → ℤ_[p]) :
    embed (matrixEquiv (fromStabilizer p U h) x) = action U (embed x) := by
  change (fun i => (algebraMap ℤ_[p] ℚ_[p])
      (((fromStabilizer p U h : Matrix n n ℤ_[p]) *ᵥ x) i)) = _
  funext i
  rw [(algebraMap ℤ_[p] ℚ_[p]).map_mulVec]
  rfl

/-- The action square commutes with the actual ambient p-adic action U. -/
theorem frame_action_commutes (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) (x : n → ℤ_[p]) :
    frameEmbed B (matrixEquiv (frameIntegral U B h) x) = action U (frameEmbed B x) := by
  change action B (embed (matrixEquiv (fromStabilizer p (B⁻¹ * U * B)
      (conjugate_stabilizes_standard U B h)) x)) = _
  rw [embed_fromStabilizer]
  have hunit : B * (B⁻¹ * U * B) = U * B := by simp [← mul_assoc]
  change (action B ∘ action (B⁻¹ * U * B)) (embed x) =
    (action U ∘ action B) (embed x)
  rw [← action_mul, ← action_mul, hunit]

/-- The same coordinate action also commutes with the common finite reduction. -/
theorem frame_reduction_commutes (k : ℕ) (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B) (x : n → ℤ_[p]) :
    CoreResidueHaar.reduction p n k (matrixEquiv (frameIntegral U B h) x) =
      matrixEquiv (reduceUnit p k (frameIntegral U B h))
        (CoreResidueHaar.reduction p n k x) :=
  reduction_commutes p k (frameIntegral U B h) x

/-- The finite residue action describes the actual image of a cylinder in B's lattice. -/
theorem frame_image_cylinder (k : ℕ) (U B : (Matrix n n ℚ_[p])ˣ)
    (h : action U '' frameLattice B = frameLattice B)
    (s : Set (n → ZMod (p ^ k))) :
    action U '' (frameEmbed B '' (CoreResidueHaar.reduction p n k ⁻¹' s)) =
      frameEmbed B '' (CoreResidueHaar.reduction p n k ⁻¹'
        (matrixEquiv (reduceUnit p k (frameIntegral U B h)) '' s)) := by
  rw [← image_cylinder (CoreResidueHaar.reduction p n k)
    (matrixEquiv (frameIntegral U B h))
    (matrixEquiv (reduceUnit p k (frameIntegral U B h)))
    (frame_reduction_commutes k U B h) s]
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  funext x
  exact (frame_action_commutes U B h x).symm

end
end CoreIntegralActionFrame

#print axioms CoreIntegralActionFrame.embed
#print axioms CoreIntegralActionFrame.range_embed
#print axioms CoreIntegralActionFrame.embed_injective
#print axioms CoreIntegralActionFrame.frameEmbed
#print axioms CoreIntegralActionFrame.range_frameEmbed
#print axioms CoreIntegralActionFrame.frameEmbed_injective
#print axioms CoreIntegralActionFrame.frameIntegral
#print axioms CoreIntegralActionFrame.embed_fromStabilizer
#print axioms CoreIntegralActionFrame.frame_action_commutes
#print axioms CoreIntegralActionFrame.frame_reduction_commutes
#print axioms CoreIntegralActionFrame.frame_image_cylinder
