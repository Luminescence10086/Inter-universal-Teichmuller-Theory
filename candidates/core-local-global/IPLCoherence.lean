import Mathlib.CategoryTheory.Iso

/-! The arrow WORD stated in III Remark 3.11.1(iii), IPL, using the first
two squares of Remark 3.10.2. Ordinary categorical calculation only.

The objects below must be supplied jointly; this file does NOT choose compatible
representatives from the original poly-isomorphisms. `defect` records the error
of arbitrary chosen representatives instead of declaring their squares commute.
No equivalence with the original IUT formal quotient or legal outputs is proved. -/
set_option autoImplicit false

namespace CoreIPL
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]
variable {L₀ L₁ L₂ U₀ U₁ U₂ U₃ : C}

/-- Source order (in execution order): inverse lower-2, inverse lower-1,
vertical-0, then upper-1, upper-2, upper-3. -/
def ipl (l₁ : L₀ ≅ L₁) (l₂ : L₁ ≅ L₂) (k₀ : L₀ ≅ U₀)
    (u₁ : U₀ ≅ U₁) (u₂ : U₁ ≅ U₂) (u₃ : U₂ ⟶ U₃) : L₂ ⟶ U₃ :=
  l₂.inv ≫ l₁.inv ≫ k₀.hom ≫ u₁.hom ≫ u₂.hom ≫ u₃

/-- The exact automorphism defect at upper-LGP for selected representatives.
No independently chosen path is silently identified with k₂. -/
def defect (l₁ : L₀ ≅ L₁) (l₂ : L₁ ≅ L₂) (k₀ : L₀ ≅ U₀)
    (k₂ : L₂ ≅ U₂) (u₁ : U₀ ≅ U₁) (u₂ : U₁ ≅ U₂) : U₂ ≅ U₂ :=
  k₂.symm ≪≫ l₂.symm ≪≫ l₁.symm ≪≫ k₀ ≪≫ u₁ ≪≫ u₂

/-- Every representative path factors into the expected vertical path, its
explicit coherence defect, and the final evaluation arrow. -/
theorem ipl_factor (l₁ : L₀ ≅ L₁) (l₂ : L₁ ≅ L₂) (k₀ : L₀ ≅ U₀)
    (k₂ : L₂ ≅ U₂) (u₁ : U₀ ≅ U₁) (u₂ : U₁ ≅ U₂) (u₃ : U₂ ⟶ U₃) :
    ipl l₁ l₂ k₀ u₁ u₂ u₃ =
      k₂.hom ≫ (defect l₁ l₂ k₀ k₂ u₁ u₂).hom ≫ u₃ := by
  simp [ipl, defect, Category.assoc]

/-- If actual representatives satisfy the two source squares, the long IPL
word reduces to vertical-2 followed by the final upper evaluation arrow. -/
theorem ipl_normalize (l₁ : L₀ ≅ L₁) (l₂ : L₁ ≅ L₂)
    (k₀ : L₀ ≅ U₀) (k₁ : L₁ ≅ U₁) (k₂ : L₂ ≅ U₂)
    (u₁ : U₀ ≅ U₁) (u₂ : U₁ ≅ U₂) (u₃ : U₂ ⟶ U₃)
    (h₁ : l₁.hom ≫ k₁.hom = k₀.hom ≫ u₁.hom)
    (h₂ : l₂.hom ≫ k₂.hom = k₁.hom ≫ u₂.hom) :
    ipl l₁ l₂ k₀ u₁ u₂ u₃ = k₂.hom ≫ u₃ := by
  have hs₁ : l₁.inv ≫ k₀.hom ≫ u₁.hom = k₁.hom := by
    rw [← h₁]
    simp
  have hs₂ : l₂.inv ≫ k₁.hom ≫ u₂.hom = k₂.hom := by
    rw [← h₂]
    simp
  calc
    ipl l₁ l₂ k₀ u₁ u₂ u₃ =
        (l₂.inv ≫ (l₁.inv ≫ k₀.hom ≫ u₁.hom) ≫ u₂.hom) ≫ u₃ := by
      simp [ipl, Category.assoc]
    _ = k₂.hom ≫ u₃ := by rw [hs₁, hs₂]

theorem defect_refl_of_squares (l₁ : L₀ ≅ L₁) (l₂ : L₁ ≅ L₂)
    (k₀ : L₀ ≅ U₀) (k₁ : L₁ ≅ U₁) (k₂ : L₂ ≅ U₂)
    (u₁ : U₀ ≅ U₁) (u₂ : U₁ ≅ U₂)
    (h₁ : l₁.hom ≫ k₁.hom = k₀.hom ≫ u₁.hom)
    (h₂ : l₂.hom ≫ k₂.hom = k₁.hom ≫ u₂.hom) :
    defect l₁ l₂ k₀ k₂ u₁ u₂ = Iso.refl U₂ := by
  apply Iso.ext
  have h := ipl_normalize l₁ l₂ k₀ k₁ k₂ u₁ u₂ (𝟙 U₂) h₁ h₂
  have hc : l₂.inv ≫ l₁.inv ≫ k₀.hom ≫ u₁.hom ≫ u₂.hom = k₂.hom := by
    simpa [ipl] using h
  simpa [defect, Category.assoc] using congrArg (fun f => k₂.inv ≫ f) hc

end CoreIPL

#print axioms CoreIPL.ipl_factor
#print axioms CoreIPL.ipl_normalize
#print axioms CoreIPL.defect_refl_of_squares
