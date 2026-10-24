/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Basic

/-!
# Corestriction in degree one

Let `φ : H →* G` be an injective group homomorphism whose image has finite index, and let `M` be
a commutative group with compatible actions of `G` and `H` (`φ h • m = h • m`). Choosing a
representative `r x` of each left coset `x ∈ G ⧸ φ(H)`, the **corestriction** of a function
`c : H → M` is

`cor c (g) = ∏_{x ∈ G ⧸ φ(H)} r(g x) • c(φ⁻¹(r(g x)⁻¹ g r(x)))`.

This sends 1-cocycles to 1-cocycles, and the coboundary of `m` to the coboundary of the
"norm" `∏ₓ r(x) • m` (`ContH1.corFun_coboundary`). This is the standard cochain formula for the
corestriction (transfer) in degree one, cf. Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, Chapter I.

Continuity of `cor c` for continuous `c` depends on the topologies at hand; the map on `ContH1`
(`ContH1.cor`) takes it as a hypothesis, and `ContH1.corFun_mul_right` is the tool to verify it
for profinite groups. The class does not depend on the choice of representatives
(`ContinuousKummerTheory.ContH1.CorestrictionIndep`).
-/

open groupCohomology

namespace ContH1

section CorFun

variable {G H M : Type*} [Group G] [Group H] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction H M] (φ : H →* G) (hφ : Function.Injective φ)

/-- The chosen representative of a left coset of `φ(H)`. -/
noncomputable def corRep (x : G ⧸ φ.range) : G := x.out

@[simp]
theorem mk_corRep (x : G ⧸ φ.range) : (QuotientGroup.mk (corRep φ x) : G ⧸ φ.range) = x :=
  QuotientGroup.out_eq' x

theorem corRep_inv_mul_mem (g : G) (x : G ⧸ φ.range) :
    (corRep φ (g • x))⁻¹ * g * corRep φ x ∈ φ.range := by
  rw [mul_assoc, ← QuotientGroup.eq, mk_corRep]
  conv_lhs => rw [← mk_corRep φ x]
  rfl

/-- The element `φ⁻¹(r(g x)⁻¹ g r(x)) ∈ H`. -/
noncomputable def corElt (g : G) (x : G ⧸ φ.range) : H :=
  (MonoidHom.ofInjective hφ).symm ⟨_, corRep_inv_mul_mem φ g x⟩

theorem apply_corElt (g : G) (x : G ⧸ φ.range) :
    φ (corElt φ hφ g x) = (corRep φ (g • x))⁻¹ * g * corRep φ x :=
  MonoidHom.apply_ofInjective_symm hφ _

theorem corRep_mul_apply_corElt (g : G) (x : G ⧸ φ.range) :
    corRep φ (g • x) * φ (corElt φ hφ g x) = g * corRep φ x := by
  rw [apply_corElt, mul_assoc, mul_inv_cancel_left]

theorem corElt_mul (g₁ g₂ : G) (x : G ⧸ φ.range) :
    corElt φ hφ (g₁ * g₂) x = corElt φ hφ g₁ (g₂ • x) * corElt φ hφ g₂ x := by
  apply hφ
  simp only [map_mul, apply_corElt, mul_smul, mul_assoc, mul_inv_cancel_left]

variable [Fintype (G ⧸ φ.range)]

/-- The corestriction of a function `c : H → M` along `φ : H →* G`, computed with the chosen
coset representatives `corRep φ`. -/
noncomputable def corFun (c : H → M) (g : G) : M :=
  ∏ x : G ⧸ φ.range, corRep φ (g • x) • c (corElt φ hφ g x)

/-- The "norm" `∏ₓ r(x) • m` attached to the chosen coset representatives. -/
noncomputable def corNorm (m : M) : M := ∏ x : G ⧸ φ.range, corRep φ x • m

variable {φ hφ} (hcomp : ∀ (h : H) (m : M), φ h • m = h • m)
include hcomp

theorem corFun_isMulCocycle₁ {c : H → M} (hc : IsMulCocycle₁ c) :
    IsMulCocycle₁ (corFun φ hφ c) := by
  intro g₁ g₂
  have key : ∀ x, corRep φ ((g₁ * g₂) • x) • c (corElt φ hφ (g₁ * g₂) x) =
      g₁ • (corRep φ (g₂ • x) • c (corElt φ hφ g₂ x)) *
        corRep φ (g₁ • (g₂ • x)) • c (corElt φ hφ g₁ (g₂ • x)) := by
    intro x
    rw [corElt_mul, hc, smul_mul', ← hcomp, smul_smul, mul_smul g₁ g₂ x,
      corRep_mul_apply_corElt, mul_smul]
  simp only [corFun]
  rw [Finset.prod_congr rfl (fun x _ => key x), Finset.prod_mul_distrib, ← Finset.smul_prod']
  congr 1
  exact Fintype.prod_equiv (MulAction.toPerm g₂) _ _ (fun x => rfl)

theorem corFun_coboundary (m : M) :
    corFun φ hφ (fun h : H => h • m / m) = fun g : G => g • corNorm φ m / corNorm φ m := by
  funext g
  have key : ∀ x, corRep φ (g • x) • (corElt φ hφ g x • m / m) =
      g • (corRep φ x • m) / corRep φ (g • x) • m := by
    intro x
    rw [smul_div', ← hcomp, smul_smul, corRep_mul_apply_corElt, mul_smul]
  simp only [corFun, corNorm]
  rw [Finset.prod_congr rfl (fun x _ => key x), Finset.prod_div_distrib, Finset.smul_prod']
  congr 1
  exact Fintype.prod_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ φ.range))
    (fun x => corRep φ (g • x) • m) (fun x => corRep φ x • m) (fun x => rfl)

omit hcomp [MulDistribMulAction H M] in
theorem corFun_mul (c d : H → M) :
    corFun φ hφ (c * d) = corFun φ hφ c * corFun φ hφ d := by
  funext g
  simp only [corFun, Pi.mul_apply, smul_mul', Finset.prod_mul_distrib]

omit hcomp [MulDistribMulAction H M] in
theorem corFun_one : corFun φ hφ (1 : H → M) = 1 := by
  funext g
  simp [corFun]

omit hcomp in
/-- The corestriction of a cocycle `c` is invariant under right multiplication by a normal
subgroup `N ≤ φ(H)` on whose preimage `c` is trivial. -/
theorem corFun_mul_right {c : H → M} (hc : IsMulCocycle₁ c) (N : Subgroup G) [N.Normal]
    (hN : N ≤ φ.range) (hc1 : ∀ k, φ k ∈ N → c k = 1) (g : G) {ν : G} (hν : ν ∈ N) :
    corFun φ hφ c (g * ν) = corFun φ hφ c g := by
  have hfix : ∀ x : G ⧸ φ.range, ν • x = x := by
    intro x
    conv_lhs => rw [← mk_corRep φ x]
    conv_rhs => rw [← mk_corRep φ x]
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mul_inv_rev]
    exact hN (Subgroup.Normal.conj_mem' inferInstance _ (N.inv_mem hν) _)
  have h1 : ∀ x, c (corElt φ hφ ν x) = 1 := by
    intro x
    apply hc1
    rw [apply_corElt, hfix]
    exact Subgroup.Normal.conj_mem' inferInstance _ hν _
  simp only [corFun]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [corElt_mul, hfix, mul_smul, hfix, hc, h1, smul_one, one_mul]

omit hcomp [MulDistribMulAction H M] in
theorem corFun_map {M' : Type*} [CommGroup M'] [MulDistribMulAction G M']
    (f : M →* M') (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (c : H → M) :
    corFun φ hφ (fun h => f (c h)) = fun g => f (corFun φ hφ c g) := by
  funext g
  simp only [corFun, map_prod, hf]

end CorFun

section Cor

variable {G H M : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]
  (φ : H →* G) (hφ : Function.Injective φ) [Fintype (G ⧸ φ.range)]
  (hcomp : ∀ (h : H) (m : M), φ h • m = h • m)
  (hcont : ∀ c : cocycles H M, Continuous (corFun φ hφ (c : H → M)))

/-- Corestriction on continuous cocycles. -/
noncomputable def corCocycles : cocycles H M →* cocycles G M where
  toFun c := ⟨corFun φ hφ c, hcont c, corFun_isMulCocycle₁ hcomp (isMulCocycle₁ c)⟩
  map_one' := Subtype.ext corFun_one
  map_mul' c d := Subtype.ext (corFun_mul c d)

@[simp]
theorem corCocycles_apply (c : cocycles H M) (g : G) :
    corCocycles φ hφ hcomp hcont c g = corFun φ hφ c g := rfl

/-- **Corestriction** `H¹_cont(H, M) → H¹_cont(G, M)` along an injective homomorphism with image
of finite index, given that it preserves continuity of cocycles. -/
noncomputable def cor : ContH1 H M →* ContH1 G M :=
  QuotientGroup.map _ _ (corCocycles φ hφ hcomp hcont) <| by
    rintro c ⟨m, hm⟩
    refine ⟨corNorm φ m, fun g => ?_⟩
    have hc : (c : H → M) = fun h => h • m / m := funext fun h => (hm h).symm
    change _ = corFun φ hφ (c : H → M) g
    rw [hc, corFun_coboundary hcomp]

@[simp]
theorem cor_mk (c : cocycles H M) :
    cor φ hφ hcomp hcont (mk c) = mk (corCocycles φ hφ hcomp hcont c) := rfl

end Cor

end ContH1
