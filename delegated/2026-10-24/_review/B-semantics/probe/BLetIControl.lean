/-
B-semantics CONTROL for T008. READ-ONLY w.r.t. all deliverables.

This file keeps ONLY the P3 control from BLetIProbe.lean (the version WITH
`letI := muAction ...`, which is how the production source writes it) and drops
the two deliberately failing probes. Expected: exit 0, no error, no warning.

If this is clean, then the two errors in BLetIProbe.lean are attributable
exactly to the omitted `letI`, not to some unrelated defect in the probe.
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

example (σ : ↥(A.decompositionSubgroup F)) (ζ : Mu n Omega) :
    letI := muAction F A hk hkres n
    reduceMu A n hn ((A.decompositionSubgroup F).subtype σ • ζ) = σ • reduceMu A n hn ζ := by
  exact reduceMu_smul F A hk hkres n hn σ ζ

end Context

end Delegated.BSemantics
