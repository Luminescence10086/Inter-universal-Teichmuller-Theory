import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Types.Basic

/-! Structural prototype for a fixed native global object. No numerical comparison
is a field. To model the source's *linear* structure arrows, the local categories
must be appropriate linear/equivariant categories; that IUT realization is open. -/
set_option autoImplicit false

namespace CoreLocalGlobal
open CategoryTheory
universe u

section Poly
variable {C : Type u} [Category C]

/-- Postcomposition by an actual target automorphism, retaining a structure arrow. -/
def targetOrbit (X H : C) : Setoid (X ⟶ H) where
  r f g := ∃ e : H ≅ H, f ≫ e.hom = g
  iseqv := ⟨fun f => ⟨Iso.refl H, by simp⟩,
    by
      rintro f g ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      simp,
    by
      rintro f g h ⟨e, he⟩ ⟨d, hd⟩
      refine ⟨e.trans d, ?_⟩
      simpa [Category.assoc, ← he] using hd⟩

abbrev PolyHom (X H : C) := Quotient (targetOrbit X H)

/-- Precomposition descends because it commutes with target automorphisms. -/
def precomp {X Y H : C} (f : X ⟶ Y) : PolyHom Y H → PolyHom X H :=
  Quotient.map (fun g => f ≫ g) (by
    rintro a b ⟨e, he⟩
    exact ⟨e, by simpa [Category.assoc] using congrArg (fun k => f ≫ k) he⟩)

@[simp] theorem precomp_id {X H : C} (p : PolyHom X H) : precomp (𝟙 X) p = p := by
  induction p using Quotient.inductionOn with
  | h f => simp [precomp]

theorem precomp_comp {X Y Z H : C} (f : X ⟶ Y) (g : Y ⟶ Z) (p : PolyHom Z H) :
    precomp f (precomp g p) = precomp (f ≫ g) p := by
  induction p using Quotient.inductionOn with
  | h k => simp [precomp, Category.assoc]

@[simp] theorem precomp_iso_cancel {X Y H : C} (e : X ≅ Y) (p : PolyHom X H) :
    precomp e.hom (precomp e.inv p) = p := by
  rw [precomp_comp, e.hom_inv_id]
  exact precomp_id p

theorem nonempty_poly_iff (X H : C) : Nonempty (PolyHom X H) ↔ Nonempty (X ⟶ H) := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨f, _⟩ := Quotient.exists_rep p
    exact ⟨f⟩
  · rintro ⟨f⟩
    exact ⟨Quotient.mk _ f⟩
end Poly

section Native
variable {G : Type u} [Category G] {I : Type u}
variable (L : I → Type u) [∀ i, Category (L i)]
variable (loc : ∀ i, G ⥤ L i) (native : G) (H : ∀ i, L i)

/-- A local-global represented object over a FIXED global object. The local
structure arrows are retained as target-automorphism orbits, not just numbers. -/
structure NativeFiber where
  localObj : ∀ i, L i
  glue : ∀ i, localObj i ≅ (loc i).obj native
  structureArrow : ∀ i, PolyHom (localObj i) (H i)

variable {L loc native H}

/-- Transport the structure orbit onto the actual localization of the fixed native object. -/
def normalized (X : NativeFiber L loc native H) (i : I) :
    PolyHom ((loc i).obj native) (H i) :=
  precomp (X.glue i).inv (X.structureArrow i)

/-- Construct a joint representation from actual local arrows on the same native localization. -/
def ofArrows (f : ∀ i, (loc i).obj native ⟶ H i) : NativeFiber L loc native H where
  localObj i := (loc i).obj native
  glue _ := Iso.refl _
  structureArrow i := Quotient.mk _ (f i)

/-- The precise structural existence obligation in this prototype is local arrow
existence from the SAME fixed global object's localizations. No q-value is assumed. -/
theorem nativeFiber_nonempty_iff : Nonempty (NativeFiber L loc native H) ↔
    ∀ i, Nonempty ((loc i).obj native ⟶ H i) := by
  constructor
  · rintro ⟨X⟩ i
    exact (nonempty_poly_iff _ _).mp ⟨normalized X i⟩
  · intro hf
    classical
    exact ⟨ofArrows (fun i => Classical.choice (hf i))⟩

/-- A morphism retains the native localization square and the structure-arrow orbit. -/
@[ext] structure FiberHom (X Y : NativeFiber L loc native H) where
  localMap : ∀ i, X.localObj i ⟶ Y.localObj i
  over_native : ∀ i, localMap i ≫ (Y.glue i).hom = (X.glue i).hom
  over_structure : ∀ i, precomp (localMap i) (Y.structureArrow i) = X.structureArrow i

instance : Category (NativeFiber L loc native H) where
  Hom := FiberHom
  id X := ⟨fun _ => 𝟙 _, by simp, by simp⟩
  comp f g := ⟨fun i => f.localMap i ≫ g.localMap i,
    by intro i; rw [Category.assoc, g.over_native, f.over_native],
    by intro i; rw [← precomp_comp, g.over_structure, f.over_structure]⟩
  id_comp f := by ext i; exact Category.id_comp _
  comp_id f := by ext i; exact Category.comp_id _
  assoc f g h := by ext i; exact Category.assoc _ _ _

/-- The actual local map of a morphism is forced by the two localization isomorphisms. -/
theorem localMap_forced {X Y : NativeFiber L loc native H} (f : X ⟶ Y) (i : I) :
    f.localMap i = (X.glue i).hom ≫ (Y.glue i).inv := by
  rw [← f.over_native i]
  simp

/-- Changes of local representatives cannot change the normalized structure orbit. -/
theorem normalized_eq_of_hom {X Y : NativeFiber L loc native H} (f : X ⟶ Y) :
    normalized X = normalized Y := by
  funext i
  unfold normalized
  rw [← f.over_structure i, precomp_comp, localMap_forced f i]
  simp

/-- An equality of normalized structure orbits reconstructs the local morphisms. -/
def homOfNormalized {X Y : NativeFiber L loc native H}
    (h : normalized X = normalized Y) : X ⟶ Y where
  localMap i := (X.glue i).hom ≫ (Y.glue i).inv
  over_native i := by simp
  over_structure i := by
    rw [← precomp_comp]
    change precomp (X.glue i).hom (normalized Y i) = X.structureArrow i
    rw [← congrFun h i]
    exact precomp_iso_cancel _ _

/-- All local maps over the same native object are forced; no extra independent
choice of local morphisms can be hidden in this representation category. -/
instance (X Y : NativeFiber L loc native H) : Subsingleton (X ⟶ Y) where
  allEq f g := by
    apply FiberHom.ext
    funext i
    rw [localMap_forced f i, localMap_forced g i]

/-- Normalized equality identifies representations by actual isomorphisms. -/
def isoOfNormalized {X Y : NativeFiber L loc native H}
    (h : normalized X = normalized Y) : X ≅ Y where
  hom := homOfNormalized h
  inv := homOfNormalized h.symm

theorem iso_nonempty_iff_normalized {X Y : NativeFiber L loc native H} :
    Nonempty (X ≅ Y) ↔ normalized X = normalized Y := by
  constructor
  · rintro ⟨e⟩
    exact normalized_eq_of_hom e.hom
  · intro h
    exact ⟨isoOfNormalized h⟩

/-- The canonical representative keeps the same global native object and the
normalized structure orbits, with identity localization identifications. -/
def canonical (X : NativeFiber L loc native H) : NativeFiber L loc native H where
  localObj i := (loc i).obj native
  glue _ := Iso.refl _
  structureArrow := normalized X

@[simp] theorem normalized_canonical (X : NativeFiber L loc native H) :
    normalized (canonical X) = normalized X := by
  funext i
  exact precomp_id _

/-- Canonicalization is an actual change of representatives, not erasure of
the structure morphism orbit. -/
def canonicalIso (X : NativeFiber L loc native H) : X ≅ canonical X :=
  isoOfNormalized (normalized_canonical X).symm

/-- Allow ONE global change of native frame, with its actual localizations.
Independent choices of a native automorphism at each place are not substituted. -/
structure FrameChange (X Y : NativeFiber L loc native H) where
  gauge : native ≅ native
  localMap : ∀ i, X.localObj i ⟶ Y.localObj i
  over_native : ∀ i, localMap i ≫ (Y.glue i).hom =
    (X.glue i).hom ≫ (loc i).map gauge.hom
  over_structure : ∀ i, precomp (localMap i) (Y.structureArrow i) = X.structureArrow i

theorem frameChange_map_forced {X Y : NativeFiber L loc native H}
    (f : FrameChange X Y) (i : I) :
    f.localMap i = (X.glue i).hom ≫ (loc i).map f.gauge.hom ≫ (Y.glue i).inv := by
  rw [← Category.assoc, ← f.over_native i]
  simp

theorem normalized_of_frameChange {X Y : NativeFiber L loc native H}
    (f : FrameChange X Y) (i : I) :
    normalized X i = precomp ((loc i).map f.gauge.hom) (normalized Y i) := by
  unfold normalized
  rw [← f.over_structure i, precomp_comp, frameChange_map_forced f i, precomp_comp]
  simp

def frameChangeOfGauge {X Y : NativeFiber L loc native H} (e : native ≅ native)
    (h : ∀ i, normalized X i = precomp ((loc i).map e.hom) (normalized Y i)) :
    FrameChange X Y where
  gauge := e
  localMap i := (X.glue i).hom ≫ (loc i).map e.hom ≫ (Y.glue i).inv
  over_native i := by simp
  over_structure i := by
    rw [← precomp_comp, ← precomp_comp]
    change precomp (X.glue i).hom
      (precomp ((loc i).map e.hom) (normalized Y i)) = X.structureArrow i
    rw [← h i]
    exact precomp_iso_cancel _ _

/-- A precise criterion for changing native frame: one global gauge must work
at every place and preserve the normalized structural arrow family. -/
theorem frameChange_exists_iff {X Y : NativeFiber L loc native H} :
    Nonempty (FrameChange X Y) ↔ ∃ e : native ≅ native,
      ∀ i, normalized X i = precomp ((loc i).map e.hom) (normalized Y i) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.gauge, normalized_of_frameChange f⟩
  · rintro ⟨e, h⟩
    exact ⟨frameChangeOfGauge e h⟩

/-- The structure orbits induced by ONE actual global arrow. -/
def localizationOrbits (target : G) (f : native ⟶ target) (i : I) :
    PolyHom ((loc i).obj native) ((loc i).obj target) :=
  Quotient.mk _ ((loc i).map f)

/-- A separate descent OBLIGATION, not an assumed theorem: all the normalized
local structure orbits arise from one global arrow between the fixed objects. -/
def GloballyRealized (target : G)
    (X : NativeFiber L loc native (fun i => (loc i).obj target)) : Prop :=
  ∃ f : native ⟶ target, localizationOrbits target f = normalized X

theorem globallyRealized_iso_iff (target : G)
    {X Y : NativeFiber L loc native (fun i => (loc i).obj target)} (e : X ≅ Y) :
    GloballyRealized target X ↔ GloballyRealized target Y := by
  unfold GloballyRealized
  rw [normalized_eq_of_hom e.hom]

/-- A global arrow gives a local-global object by construction, without
asserting that arbitrary independent local arrows descend. -/
def ofGlobalArrow (target : G) (f : native ⟶ target) :
    NativeFiber L loc native (fun i => (loc i).obj target) :=
  ofArrows (fun i => (loc i).map f)

theorem ofGlobalArrow_realized (target : G) (f : native ⟶ target) :
    GloballyRealized target (ofGlobalArrow (L := L) (loc := loc) target f) := by
  refine ⟨f, ?_⟩
  funext i
  simp [localizationOrbits, ofGlobalArrow, ofArrows, normalized]

/-- Local-global representation existence and global arrow descent are distinct
problems. This theorem exposes exactly the global morphism obligation. -/
theorem realizedFiber_exists_iff (target : G) :
    (∃ X : NativeFiber L loc native (fun i => (loc i).obj target),
      GloballyRealized target X) ↔ Nonempty (native ⟶ target) := by
  constructor
  · rintro ⟨_, f, _⟩
    exact ⟨f⟩
  · rintro ⟨f⟩
    exact ⟨ofGlobalArrow (L := L) (loc := loc) target f,
      ofGlobalArrow_realized (L := L) (loc := loc) target f⟩

end Native

section DescentCounterexample

/-- A deliberately information-losing localization, used only for a regression. -/
def collapse : Discrete Bool ⥤ Discrete PUnit where
  obj _ := Discrete.mk PUnit.unit
  map _ := 𝟙 _

/-- Even a correctly glued fixed-native representation can lack a global arrow.
This is a categorical counterexample to automatic descent, not to IUT. -/
theorem local_representations_do_not_force_descent :
    Nonempty (NativeFiber (fun _ : Unit => Discrete PUnit) (fun _ => collapse)
      (Discrete.mk false) (fun _ => collapse.obj (Discrete.mk true))) ∧
      ¬ Nonempty ((Discrete.mk false : Discrete Bool) ⟶ Discrete.mk true) := by
  constructor
  · exact ⟨ofArrows (fun _ => 𝟙 _)⟩
  · rintro ⟨f⟩
    exact Bool.false_ne_true (Discrete.eq_of_hom f)

end DescentCounterexample

section StructureOrbitCounterexample

/-- Forgetting the structure orbit loses information even when the underlying
source and target objects are literally identical. Target automorphisms cannot
turn a constant map into the identity. This does not model IUT arithmetic. -/
theorem constant_not_identity_poly :
    (Quotient.mk (targetOrbit (C := Type) Bool Bool)
      (TypeCat.ofHom (fun _ : Bool => false))) ≠
      Quotient.mk (targetOrbit (C := Type) Bool Bool) (𝟙 Bool) := by
  intro h
  obtain ⟨e, he⟩ := Quotient.exact h
  have hf := congrArg (fun f : Bool ⟶ Bool => f false) he
  have ht := congrArg (fun f : Bool ⟶ Bool => f true) he
  change e.hom false = false at hf
  change e.hom false = true at ht
  exact Bool.false_ne_true (hf.symm.trans ht)

end StructureOrbitCounterexample
end CoreLocalGlobal

#print axioms CoreLocalGlobal.precomp_comp
#print axioms CoreLocalGlobal.nativeFiber_nonempty_iff
#print axioms CoreLocalGlobal.localMap_forced
#print axioms CoreLocalGlobal.normalized_eq_of_hom
#print axioms CoreLocalGlobal.iso_nonempty_iff_normalized
#print axioms CoreLocalGlobal.canonicalIso
#print axioms CoreLocalGlobal.globallyRealized_iso_iff
#print axioms CoreLocalGlobal.ofGlobalArrow_realized
#print axioms CoreLocalGlobal.realizedFiber_exists_iff
#print axioms CoreLocalGlobal.local_representations_do_not_force_descent
#print axioms CoreLocalGlobal.constant_not_identity_poly
#print axioms CoreLocalGlobal.frameChange_map_forced
#print axioms CoreLocalGlobal.normalized_of_frameChange
#print axioms CoreLocalGlobal.frameChange_exists_iff
