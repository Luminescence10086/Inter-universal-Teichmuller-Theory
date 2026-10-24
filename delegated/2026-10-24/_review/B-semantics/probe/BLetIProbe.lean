/-
B-semantics independent probe for T008. READ-ONLY w.r.t. all deliverables.

Targets one claim in ARROW-TABLE.md §1.3 / §2 (C5) and SUMMARY.md:
  "muAction 必须经 letI 消费；忘记 letI 会静默落到 Mu n κ 上 Gal(κ/k) 的另一个作用实例。"

Test P2: without `letI := muAction ...`, can the elaborator even synthesise a
         `MulDistribMulAction ↥(decompositionSubgroup) (Mu n κ)` instance?
Test P1: without `letI`, does the `reduceMu_smul` statement still elaborate
         (i.e. is the substitution silent), or is it a hard error?

This file defines nothing and is not part of the T008 delivery.
-/
import ContinuousKummerTheory.Kummer.Decomposition
set_option autoImplicit false

namespace Delegated.BSemantics

open IsLocalRing KummerTheory KummerTheory.Decomposition

section Context

variable {k F Omega : Type*} [Field k] [Field F] [Field Omega]
  [Algebra k F] [Algebra F Omega] [Algebra k Omega] [IsScalarTower k F Omega]
  (A : ValuationSubring Omega) (hk : forall c : k, algebraMap k Omega c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : forall c : k, residue A ⟨algebraMap k Omega c, hk c⟩ = algebraMap k (ResidueField A) c)
  (n : Nat) (hn : n ≠ 0)

-- P2: no `letI` in scope. Is there any instance at all?
#synth MulDistribMulAction ↥(A.decompositionSubgroup F) (Mu n (ResidueField A))

-- P1: the `reduceMu_smul` statement written WITHOUT `letI`.
example (σ : ↥(A.decompositionSubgroup F)) (ζ : Mu n Omega) :
    reduceMu A n hn ((A.decompositionSubgroup F).subtype σ • ζ) = σ • reduceMu A n hn ζ := by
  exact reduceMu_smul F A hk hkres n hn σ ζ

-- P3: control, same statement WITH the `letI` that the source uses.
example (σ : ↥(A.decompositionSubgroup F)) (ζ : Mu n Omega) :
    letI := muAction F A hk hkres n
    reduceMu A n hn ((A.decompositionSubgroup F).subtype σ • ζ) = σ • reduceMu A n hn ζ := by
  exact reduceMu_smul F A hk hkres n hn σ ζ

end Context

end Delegated.BSemantics
