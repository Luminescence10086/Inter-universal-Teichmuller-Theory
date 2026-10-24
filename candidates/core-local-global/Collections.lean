import NativeFiber
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Local/global collections with a separate REALIFICATION functor.
Motivation: IUT III cQ3, clauses lc-gl-1/2/3. This is the categorical shape,
not an instance of the original Frobenioids, their actions or their formal quotient.

Raw local objects lie in L_i; their realifications and global localizations lie
in R_i. There is no assumed identification of a raw object with its realification.
For the intended source interpretation the local categories must encode the
appropriate allowed linear/equivariant arrows; arbitrary categories here do not
establish that interpretation. -/
set_option autoImplicit false

namespace CoreCollections
open CategoryTheory CoreLocalGlobal
universe u v
variable {G : Type u} [Category G] {I : Type v}
variable (L R : I → Type u) [∀ i, Category (L i)] [∀ i, Category (R i)]
variable (realize : ∀ i, L i ⥤ R i) (loc : ∀ i, G ⥤ R i)

structure Collection where
  globalObj : G
  localObj : ∀ i, L i
  glue : ∀ i, (realize i).obj (localObj i) ≅ (loc i).obj globalObj

variable {L R realize loc}

@[ext] structure CollectionHom (X Y : Collection L R realize loc) where
  globalMap : X.globalObj ⟶ Y.globalObj
  localMap : ∀ i, X.localObj i ⟶ Y.localObj i
  square : ∀ i, (realize i).map (localMap i) ≫ (Y.glue i).hom =
    (X.glue i).hom ≫ (loc i).map globalMap

instance : Category (Collection L R realize loc) where
  Hom := CollectionHom
  id X := ⟨𝟙 _, fun _ => 𝟙 _, by simp⟩
  comp f g := ⟨f.globalMap ≫ g.globalMap, fun i => f.localMap i ≫ g.localMap i,
    by
      intro i
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, g.square,
        ← Category.assoc, f.square, Category.assoc]⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

variable (L R realize loc)

/-- The global component is retained by a genuine functor. -/
def globalProjection : Collection L R realize loc ⥤ G where
  obj X := X.globalObj
  map f := f.globalMap

variable (H : ∀ i, L i)

structure Structured where
  base : Collection L R realize loc
  arrow : ∀ i, PolyHom (base.localObj i) (H i)

variable {L R realize loc H}

@[ext] structure StructuredHom (X Y : Structured L R realize loc H) where
  baseMap : X.base ⟶ Y.base
  over_structure : ∀ i, precomp (baseMap.localMap i) (Y.arrow i) = X.arrow i

instance : Category (Structured L R realize loc H) where
  Hom := StructuredHom
  id X := ⟨𝟙 _, by intro i; change precomp (𝟙 _) (X.arrow i) = _; exact precomp_id _⟩
  comp f g := ⟨f.baseMap ≫ g.baseMap,
    by
      intro i
      change precomp (f.baseMap.localMap i ≫ g.baseMap.localMap i) _ = _
      rw [← precomp_comp, g.over_structure, f.over_structure]⟩
  id_comp f := by ext; exact Category.id_comp _
  comp_id f := by ext; exact Category.comp_id _
  assoc f g h := by ext; exact Category.assoc _ _ _

variable (L R realize loc H)

/-- Forgetting the structure arrow is a functor; no subcategory inclusion is assumed. -/
def forget : Structured L R realize loc H ⥤ Collection L R realize loc where
  obj X := X.base
  map f := f.baseMap

instance : (forget L R realize loc H).Faithful where
  map_injective h := StructuredHom.ext h

variable {L R realize loc H}

/-- The exact lifting condition for a fixed underlying comparison arrow. -/
theorem exists_lift_iff (X Y : Structured L R realize loc H) (f : X.base ⟶ Y.base) :
    (∃ g : X ⟶ Y, g.baseMap = f) ↔
      ∀ i, precomp (f.localMap i) (Y.arrow i) = X.arrow i := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.over_structure
  · intro h
    exact ⟨⟨f, h⟩, rfl⟩

/-- Reconstruct structure on another presentation using an ACTUAL base isomorphism.
This is not descent along an unspecified formal quotient. -/
def transport (Y : Structured L R realize loc H)
    {X : Collection L R realize loc} (e : X ≅ Y.base) : Structured L R realize loc H where
  base := X
  arrow i := precomp (e.hom.localMap i) (Y.arrow i)

/-- A chosen base isomorphism lifts after transporting the structure; it need
not lift between two independently prescribed decorations. -/
def transportIso (Y : Structured L R realize loc H)
    {X : Collection L R realize loc} (e : X ≅ Y.base) : transport Y e ≅ Y where
  hom := ⟨e.hom, fun _ => rfl⟩
  inv := ⟨e.inv, by
    intro i
    change precomp (e.inv.localMap i) (precomp (e.hom.localMap i) (Y.arrow i)) = Y.arrow i
    rw [precomp_comp]
    have hi : e.inv.localMap i ≫ e.hom.localMap i = 𝟙 _ :=
      congrArg (fun f : Y.base ⟶ Y.base => f.localMap i) e.inv_hom_id
    rw [hi, precomp_id]⟩
  hom_inv_id := by apply StructuredHom.ext; exact e.hom_inv_id
  inv_hom_id := by apply StructuredHom.ext; exact e.inv_hom_id

theorem transportIso_lies_over (Y : Structured L R realize loc H)
    {X : Collection L R realize loc} (e : X ≅ Y.base) :
    (transportIso Y e).hom.baseMap = e.hom := rfl

/-- If a prescribed comparison already preserves structure, its base inverse
also preserves structure. This constructs, rather than assumes, the lifted iso. -/
def liftIso (X Y : Structured L R realize loc H) (e : X.base ≅ Y.base)
    (h : ∀ i, precomp (e.hom.localMap i) (Y.arrow i) = X.arrow i) : X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    intro i
    rw [← h i, precomp_comp]
    have hi : e.inv.localMap i ≫ e.hom.localMap i = 𝟙 _ :=
      congrArg (fun f : Y.base ⟶ Y.base => f.localMap i) e.inv_hom_id
    rw [hi, precomp_id]⟩
  hom_inv_id := by apply StructuredHom.ext; exact e.hom_inv_id
  inv_hom_id := by apply StructuredHom.ext; exact e.inv_hom_id

theorem iso_lift_exists_iff (X Y : Structured L R realize loc H) (e : X.base ≅ Y.base) :
    (∃ d : X ≅ Y, d.hom.baseMap = e.hom) ↔
      ∀ i, precomp (e.hom.localMap i) (Y.arrow i) = X.arrow i := by
  constructor
  · rintro ⟨d, hd⟩
    simpa [← hd] using d.hom.over_structure
  · intro h
    exact ⟨liftIso X Y e h, rfl⟩

section Counterexample
def boolBase : Collection (fun _ : Unit => Type) (fun _ => Type)
    (fun _ => 𝟭 Type) (fun _ => 𝟭 Type) where
  globalObj := Bool
  localObj _ := Bool
  glue _ := Iso.refl _

def constantDecoration : Structured (fun _ : Unit => Type) (fun _ => Type)
    (fun _ => 𝟭 Type) (fun _ => 𝟭 Type) (fun _ => Bool) where
  base := boolBase
  arrow _ := Quotient.mk _ (TypeCat.ofHom (fun _ : Bool => false))

def identityDecoration : Structured (fun _ : Unit => Type) (fun _ => Type)
    (fun _ => 𝟭 Type) (fun _ => 𝟭 Type) (fun _ => Bool) where
  base := boolBase
  arrow _ := Quotient.mk _ (𝟙 Bool)

/-- Even the identity on a common underlying collection need not lift between
independently prescribed structure orbits. Generic regression, not an IUT example. -/
theorem base_identity_need_not_lift :
    ¬ ∃ f : constantDecoration ⟶ identityDecoration, f.baseMap = 𝟙 boolBase := by
  rintro ⟨f, hf⟩
  have h := f.over_structure ()
  rw [hf] at h
  change precomp (𝟙 Bool) (Quotient.mk _ (𝟙 Bool)) =
    Quotient.mk _ (TypeCat.ofHom (fun _ : Bool => false)) at h
  rw [precomp_id] at h
  exact constant_not_identity_poly h.symm

/-- This concrete forgetful functor is faithful but not full. Consequently
generic full-subcategory inclusion is not an available replacement for it. -/
theorem bool_forget_not_full :
    ¬ (forget (fun _ : Unit => Type) (fun _ => Type)
      (fun _ => 𝟭 Type) (fun _ => 𝟭 Type) (fun _ => Bool)).Full := by
  intro hfull
  let _ := hfull
  obtain ⟨f, hf⟩ := (forget (fun _ : Unit => Type) (fun _ => Type)
    (fun _ => 𝟭 Type) (fun _ => 𝟭 Type) (fun _ => Bool)).map_surjective
      (X := constantDecoration) (Y := identityDecoration) (𝟙 boolBase)
  exact base_identity_need_not_lift ⟨f, hf⟩

end Counterexample
end CoreCollections

#print axioms CoreCollections.forget
#print axioms CoreCollections.exists_lift_iff
#print axioms CoreCollections.transportIso
#print axioms CoreCollections.transportIso_lies_over
#print axioms CoreCollections.liftIso
#print axioms CoreCollections.iso_lift_exists_iff
#print axioms CoreCollections.base_identity_need_not_lift
#print axioms CoreCollections.bool_forget_not_full
