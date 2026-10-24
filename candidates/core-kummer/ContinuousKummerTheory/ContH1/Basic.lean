/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Continuous first cohomology (multiplicative model)

For a topological group `G` acting on a commutative topological group `M` (written
multiplicatively) we define the first continuous cohomology group

`ContH1 G M = Z¹_cont(G, M) / B¹(G, M)`,

where `Z¹_cont(G, M)` is the group of *continuous* crossed homomorphisms (1-cocycles in the sense
of `groupCohomology.IsMulCocycle₁`, i.e. `f (g * h) = g • f h * f g`) and `B¹(G, M)` is the
subgroup of those which are principal (`groupCohomology.IsMulCoboundary₁`).

This is the classical low-degree description of `H¹_cont(G, M)` (Serre, *Galois Cohomology*,
Chapter I). When `M` is discrete and `G` is profinite it agrees with the colimit of the
first cohomology groups of the finite quotients of `G` (a classical fact, not formalised here).

## Main definitions

* `ContH1.cocycles G M` : the subgroup of continuous 1-cocycles in `G → M`.
* `ContH1.coboundaries G M` : the subgroup of principal cocycles.
* `ContH1 G M` : the quotient.
* `ContH1.mk` : the projection from cocycles to `ContH1 G M`.
* `ContH1.map` : functoriality in the pair `(G, M)`.
-/

open groupCohomology

section Cocycles

variable (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

namespace ContH1

/-- The subgroup of continuous 1-cocycles `G → M`. -/
def cocycles : Subgroup (G → M) where
  carrier := {f | Continuous f ∧ IsMulCocycle₁ f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.mul hg, fun a b => ?_⟩
    simp only [Pi.mul_apply, hf' a b, hg' a b, smul_mul']
    exact mul_mul_mul_comm _ _ _ _
  one_mem' := ⟨continuous_const, fun a b => by simp⟩
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨hf.inv, fun a b => ?_⟩
    simp only [Pi.inv_apply, hf' a b, smul_inv', mul_inv]

instance : CoeFun (cocycles G M) (fun _ => G → M) := ⟨fun c => (c : G → M)⟩

variable {G M} in
@[simp]
theorem coe_mul_apply (c d : cocycles G M) (g : G) : (c * d) g = c g * d g := rfl

variable {G M} in
@[simp]
theorem coe_inv_apply (c : cocycles G M) (g : G) : c⁻¹ g = (c g)⁻¹ := rfl

variable {G M} in
@[simp]
theorem coe_div_apply (c d : cocycles G M) (g : G) : (c / d) g = c g / d g := rfl

variable {G M} in
@[simp]
theorem coe_one_apply (g : G) : (1 : cocycles G M) g = 1 := rfl

variable {G M} in
theorem mem_cocycles_iff {f : G → M} : f ∈ cocycles G M ↔ Continuous f ∧ IsMulCocycle₁ f :=
  Iff.rfl

/-- The subgroup of principal (continuous) cocycles. -/
def coboundaries : Subgroup (cocycles G M) where
  carrier := {f | IsMulCoboundary₁ (f : G → M)}
  mul_mem' := by
    rintro f g ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, fun a => ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, ← hx a, ← hy a, smul_mul']
    exact mul_div_mul_comm _ _ _ _
  one_mem' := ⟨1, fun a => by simp⟩
  inv_mem' := by
    rintro f ⟨x, hx⟩
    refine ⟨x⁻¹, fun a => ?_⟩
    simp only [Subgroup.coe_inv, Pi.inv_apply, ← hx a, smul_inv', inv_div_inv, inv_div]

variable {G M} in
theorem mem_coboundaries_iff {f : cocycles G M} :
    f ∈ coboundaries G M ↔ IsMulCoboundary₁ (f : G → M) :=
  Iff.rfl

end ContH1

/-- The first continuous cohomology group `H¹_cont(G, M)`, as continuous crossed homomorphisms
modulo principal crossed homomorphisms. -/
def ContH1 : Type _ := ContH1.cocycles G M ⧸ ContH1.coboundaries G M

namespace ContH1

instance : CommGroup (ContH1 G M) :=
  inferInstanceAs (CommGroup (cocycles G M ⧸ coboundaries G M))

variable {G M}

/-- The class of a continuous cocycle in `ContH1 G M`. -/
def mk : cocycles G M →* ContH1 G M := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk (G := G) (M := M)) :=
  QuotientGroup.mk'_surjective _

@[elab_as_elim]
theorem induction_on {P : ContH1 G M → Prop} (x : ContH1 G M) (h : ∀ c, P (mk c)) : P x := by
  obtain ⟨c, rfl⟩ := mk_surjective x
  exact h c

theorem mk_eq_one_iff (c : cocycles G M) : mk c = 1 ↔ IsMulCoboundary₁ (c : G → M) :=
  QuotientGroup.eq_one_iff c

theorem mk_eq_mk_iff (c d : cocycles G M) :
    mk c = mk d ↔ IsMulCoboundary₁ (fun g => c g / d g) := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff]
  rfl

theorem isMulCocycle₁ (c : cocycles G M) : IsMulCocycle₁ (c : G → M) := c.2.2

theorem continuous (c : cocycles G M) : Continuous (c : G → M) := c.2.1

theorem map_one_eq (c : cocycles G M) : (c : G → M) 1 = 1 :=
  map_one_of_isMulCocycle₁ (isMulCocycle₁ c)

/-- Build an element of `cocycles G M` from a continuous function satisfying the cocycle
identity. -/
def mkCocycle (f : G → M) (hc : Continuous f) (hf : IsMulCocycle₁ f) : cocycles G M :=
  ⟨f, hc, hf⟩

@[simp]
theorem coe_mkCocycle (f : G → M) (hc : Continuous f) (hf : IsMulCocycle₁ f) :
    (mkCocycle f hc hf : G → M) = f := rfl

/-- A function on a topological group which is invariant under right translation by an open
subgroup is continuous. -/
theorem _root_.continuous_of_mul_right_invariant {X : Type*} [TopologicalSpace X]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ u ∈ U, f (g * u) = f g) : Continuous f := by
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    simpa [Set.mem_preimage, hf g u hu] using hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

end ContH1

end Cocycles

namespace ContH1

section Map

variable {G H M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  [Group H] [TopologicalSpace H] [CommGroup N] [TopologicalSpace N]
  [IsTopologicalGroup N] [MulDistribMulAction H N]

/-- The map on continuous cocycles induced by a continuous group homomorphism `φ : H → G` and a
compatible continuous homomorphism of coefficients `f : M → N`. -/
def cocyclesMap (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) : cocycles G M →* cocycles H N where
  toFun c := ⟨fun h => f (c (φ h)), hf.comp ((continuous c).comp hφ), fun a b => by
    simp only [map_mul, isMulCocycle₁ c (φ a) (φ b), hcomp]⟩
  map_one' := Subtype.ext <| funext fun _ => map_one f
  map_mul' _ _ := Subtype.ext <| funext fun _ => map_mul f _ _

@[simp]
theorem cocyclesMap_apply (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) (c : cocycles G M) (h : H) :
    (cocyclesMap φ hφ f hf hcomp c : H → N) h = f (c (φ h)) := rfl

/-- The map `H¹_cont(G, M) → H¹_cont(H, N)` induced by a continuous group homomorphism
`φ : H → G` and a compatible continuous homomorphism of coefficients `f : M → N`. -/
def map (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) : ContH1 G M →* ContH1 H N :=
  QuotientGroup.map _ _ (cocyclesMap φ hφ f hf hcomp) <| by
    rintro c ⟨m, hm⟩
    refine ⟨f m, fun h => ?_⟩
    simp only [cocyclesMap_apply, ← hm, ← hcomp, map_div]

@[simp]
theorem map_mk (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) (c : cocycles G M) :
    map φ hφ f hf hcomp (mk c) = mk (cocyclesMap φ hφ f hf hcomp c) := rfl

end Map

end ContH1
