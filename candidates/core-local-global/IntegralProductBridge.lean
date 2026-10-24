/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project

The proof of `isIntegral_pi` below is adapted from
Iut/Concrete/LocalConstruct/ResidueField.lean in the LANA Project,
commit f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb, under Apache 2.0.
The other declarations package the product criterion and Mathlib equivalences.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.RingTheory.Artinian.Module

/-!
# Integral closure and a finite product decomposition

An actual algebra equivalence with a finite product induces an algebra equivalence
of integral closures. No coordinatewise integrality or order decomposition is assumed.
This is a generic bridge; it does not instantiate the external IUT tensor packet.
-/

set_option autoImplicit false

namespace CoreLocalGlobal.IntegralProductBridge

open Polynomial

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {B : ι → Type w} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- Finiteness permits a single integral relation for all coordinates. -/
theorem isIntegral_pi (f : ∀ i, B i) (hf : ∀ i, IsIntegral R (f i)) :
    IsIntegral R f := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨P, hP, hPf⟩ := hf i
  refine ⟨X * P, monic_X.mul hP, ?_⟩
  rw [eval₂_mul, eval₂_X]
  funext j
  by_cases hij : j = i
  · subst hij
    have hcomp : (Pi.evalRingHom B j).comp (algebraMap R (∀ i, B i)) =
        algebraMap R (B j) := RingHom.ext fun _ => rfl
    change Pi.single j (f j) j * Pi.evalRingHom B j
      (eval₂ (algebraMap R (∀ i, B i)) (Pi.single j (f j)) P) = 0
    rw [hom_eval₂, hcomp, Pi.evalRingHom_apply, Pi.single_eq_same, hPf]
    exact mul_zero _
  · change Pi.single i (f i) j * _ = 0
    rw [Pi.single_eq_of_ne hij, zero_mul]

theorem isIntegral_pi_iff (f : ∀ i, B i) :
    IsIntegral R f ↔ ∀ i, IsIntegral R (f i) := by
  constructor
  · intro hf i
    exact hf.map (Pi.evalAlgHom R B i)
  · exact isIntegral_pi f

/-- Equality of subalgebras, not only an equivalence of membership predicates. -/
theorem integralClosure_pi :
    integralClosure R (∀ i, B i) =
      Subalgebra.pi Set.univ (fun i => integralClosure R (B i)) := by
  ext f
  simp only [Subalgebra.mem_pi, Set.mem_univ, forall_const, mem_integralClosure_iff]
  exact isIntegral_pi_iff f

/-- The integral closure of a finite product is the product of the integral closures. -/
def piEquiv : integralClosure R (∀ i, B i) ≃ₐ[R] ∀ i, integralClosure R (B i) where
  toFun x i := ⟨x.1 i, (isIntegral_pi_iff x.1).mp x.2 i⟩
  invFun x := ⟨fun i => (x i).1, isIntegral_pi _ (fun i => (x i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem piEquiv_apply_coe (x : integralClosure R (∀ i, B i)) (i : ι) :
    ((piEquiv x i : integralClosure R (B i)) : B i) = (x : ∀ i, B i) i := rfl

variable {A : Type z} [CommRing A] [Algebra R A]

/-- Restrict an actual finite product algebra decomposition to integral closures. -/
def equiv (e : A ≃ₐ[R] ∀ i, B i) :
    integralClosure R A ≃ₐ[R] ∀ i, integralClosure R (B i) :=
  e.mapIntegralClosure.trans piEquiv

theorem mem_iff (e : A ≃ₐ[R] ∀ i, B i) (x : A) :
    x ∈ integralClosure R A ↔ ∀ i, e x i ∈ integralClosure R (B i) := by
  change IsIntegral R x ↔ ∀ i, IsIntegral R (e x i)
  rw [← isIntegral_pi_iff]
  exact (isIntegral_algHom_iff e.toAlgHom e.injective).symm

/-- The image of the source integral closure is exactly the product subalgebra. -/
theorem map_eq_pi (e : A ≃ₐ[R] ∀ i, B i) :
    (integralClosure R A).map e.toAlgHom =
      Subalgebra.pi Set.univ (fun i => integralClosure R (B i)) := by
  rw [integralClosure_map_algEquiv, integralClosure_pi]

@[simp] theorem equiv_apply_coe (e : A ≃ₐ[R] ∀ i, B i)
    (x : integralClosure R A) (i : ι) :
    ((equiv e x i : integralClosure R (B i)) : B i) = e (x : A) i := rfl

@[simp] theorem equiv_symm_apply_coe (e : A ≃ₐ[R] ∀ i, B i)
    (x : ∀ i, integralClosure R (B i)) :
    ((equiv e).symm x : A) = e.symm (fun i => (x i : B i)) := rfl

/-- The coordinate projection square commutes as an equality of algebra maps. -/
theorem coordinate_commutes (e : A ≃ₐ[R] ∀ i, B i) (i : ι) :
    (integralClosure R (B i)).val.comp
        ((Pi.evalAlgHom R (fun i => integralClosure R (B i)) i).comp
          (equiv e).toAlgHom) =
      ((Pi.evalAlgHom R B i).comp e.toAlgHom).comp (integralClosure R A).val := by
  ext x
  rfl

section Artinian

variable [IsArtinianRing A] [IsReduced A]

/-- The canonical reduced-Artinian decomposition, viewed over the coefficient ring. -/
noncomputable def artinianEquiv :
    A ≃ₐ[R] ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal :=
  (IsArtinianRing.equivPi A).restrictScalars R

/-- Integral closure in a reduced Artinian algebra decomposes over its maximal ideals. -/
noncomputable def artinianIntegralEquiv :
    integralClosure R A ≃ₐ[R]
      ∀ m : MaximalSpectrum A, integralClosure R (A ⧸ m.asIdeal) :=
  equiv (artinianEquiv (R := R) (A := A))

@[simp] theorem artinianIntegralEquiv_apply_coe (x : integralClosure R A)
    (m : MaximalSpectrum A) :
    ((artinianIntegralEquiv x m : integralClosure R (A ⧸ m.asIdeal)) : A ⧸ m.asIdeal) =
      Ideal.Quotient.mk m.asIdeal (x : A) := rfl

theorem artinian_mem_iff (x : A) :
    x ∈ integralClosure R A ↔ ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal x ∈ integralClosure R (A ⧸ m.asIdeal) :=
  mem_iff (artinianEquiv (R := R) (A := A)) x

theorem artinian_map_eq_pi :
    (integralClosure R A).map (artinianEquiv (R := R) (A := A)).toAlgHom =
      Subalgebra.pi Set.univ
        (fun m : MaximalSpectrum A => integralClosure R (A ⧸ m.asIdeal)) :=
  map_eq_pi (artinianEquiv (R := R) (A := A))

theorem artinian_coordinate_commutes (m : MaximalSpectrum A) :
    (integralClosure R (A ⧸ m.asIdeal)).val.comp
        ((Pi.evalAlgHom R (fun m : MaximalSpectrum A =>
          integralClosure R (A ⧸ m.asIdeal)) m).comp artinianIntegralEquiv.toAlgHom) =
      (Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R A).val := by
  ext x
  rfl

end Artinian

end CoreLocalGlobal.IntegralProductBridge

#print axioms CoreLocalGlobal.IntegralProductBridge.isIntegral_pi
#print axioms CoreLocalGlobal.IntegralProductBridge.isIntegral_pi_iff
#print axioms CoreLocalGlobal.IntegralProductBridge.integralClosure_pi
#print axioms CoreLocalGlobal.IntegralProductBridge.piEquiv
#print axioms CoreLocalGlobal.IntegralProductBridge.piEquiv_apply_coe
#print axioms CoreLocalGlobal.IntegralProductBridge.equiv
#print axioms CoreLocalGlobal.IntegralProductBridge.mem_iff
#print axioms CoreLocalGlobal.IntegralProductBridge.map_eq_pi
#print axioms CoreLocalGlobal.IntegralProductBridge.equiv_apply_coe
#print axioms CoreLocalGlobal.IntegralProductBridge.equiv_symm_apply_coe
#print axioms CoreLocalGlobal.IntegralProductBridge.coordinate_commutes
#print axioms CoreLocalGlobal.IntegralProductBridge.artinianEquiv
#print axioms CoreLocalGlobal.IntegralProductBridge.artinianIntegralEquiv
#print axioms CoreLocalGlobal.IntegralProductBridge.artinianIntegralEquiv_apply_coe
#print axioms CoreLocalGlobal.IntegralProductBridge.artinian_mem_iff
#print axioms CoreLocalGlobal.IntegralProductBridge.artinian_map_eq_pi
#print axioms CoreLocalGlobal.IntegralProductBridge.artinian_coordinate_commutes
