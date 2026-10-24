/-
T008 probe. SOURCE / type-audit only, RESEARCH_ONLY.

This file defines nothing. It is a pure `#check` / `#print axioms` trace over production
declarations, run under -DwarningAsError=true, so the arrow table in ../ARROW-TABLE.md is
backed by elaborator output against the actual SHA-pinned sources, not by reading text.

Why no new definitions: attempt 1 wrapped the two legs of the decomposition square in
local defs; the elaborator silently replaced their values with `sorry` and dropped the
hk/hkres hypotheses from the printed signature (logs/attempt1.stdout.log). That artifact
would have been a fabricated arrow, so it was discarded, not repaired. Nothing here is a
definition, so nothing here can carry a sorry.

Context mirrors ContinuousKummerTheory/Kummer/Decomposition.lean's variable block so the
#checks resolve at the same types the production theorems use.

Not covered here (see ../GAP.md): Boundary/DecompositionBridge.lean is listed in
baseline.json but has no .olean under candidates/core-kummer/.lake/build, so its
declarations cannot be checked from this workspace without a build this task does not own.
-/
import ContinuousKummerTheory.Kummer.Decomposition
import ContinuousKummerTheory.Kummer.DecompositionSurjective
import Boundary.ReducedComparison
set_option autoImplicit false

namespace Delegated.T008

open IsLocalRing KummerTheory KummerTheory.Decomposition

section Context

variable {k F Omega : Type*} [Field k] [Field F] [Field Omega]
  [Algebra k F] [Algebra F Omega] [Algebra k Omega] [IsScalarTower k F Omega]
  (A : ValuationSubring Omega) (hk : forall c : k, algebraMap k Omega c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : forall c : k, residue A ⟨algebraMap k Omega c, hk c⟩ = algebraMap k (ResidueField A) c)
  (n : Nat) (hn : n ≠ 0)

-- A1. subtype : D_A -> Gal(Omega/F), an inclusion, not a quotient map.
#check @Subgroup.subtype
#check @ValuationSubring.decompositionSubgroup
#check @ValuationSubring.inertiaSubgroup

-- A2. decompositionMap : D_A ->* Gal(kappa(A)/k).
#check @KummerTheory.Decomposition.decompositionMap

-- A3. muAction, instance-valued, letI-consumed, no data beyond A2.
#check @KummerTheory.Decomposition.muAction

-- A4. reduceMu : mu_n(Omega) ->* mu_n(kappa(A)), needs only hn.
#check @KummerTheory.Decomposition.reduceMu
#check @KummerTheory.specMu

-- A5. Derived facts each arrow in the table cites.
#check @KummerTheory.Decomposition.decompositionMap_apply
#check @KummerTheory.Decomposition.decompositionMap_residue
#check @KummerTheory.Decomposition.ker_decompositionMap
#check @KummerTheory.Decomposition.continuous_decompositionMap
#check @KummerTheory.Decomposition.reduceMu_smul
#check @KummerTheory.specMu_smul

-- A6. The one place a surjectivity of A2 exists, with its exact hypotheses.
#check @KummerTheory.Decomposition.decompositionMap_surjective
#check @KummerTheory.Decomposition.exists_decompositionMap_eq_of_fixes

-- A7. Reflection is taken on A2, never by inverting A4.
#check @CoreCohomologyReflection.map_injective
#check @CoreReducedComparison.pullback_injective
#check @CoreReducedComparison.residue_classes_eq_of_specialization_squares

-- A8. The decomposition square itself, at its real type.
#check @KummerTheory.Decomposition.decomposition_kummer
#check @KummerTheory.Decomposition.decomposition_kummerValue

-- A9. ContH1.map, the single functor every arrow is an instance of.
#check @ContH1.map
#check @ContH1.cocyclesMap

end Context

end Delegated.T008

-- Axiom reports.
#print axioms KummerTheory.Decomposition.decompositionMap
#print axioms KummerTheory.Decomposition.muAction
#print axioms KummerTheory.Decomposition.reduceMu
#print axioms KummerTheory.Decomposition.ker_decompositionMap
#print axioms KummerTheory.Decomposition.continuous_decompositionMap
#print axioms KummerTheory.Decomposition.reduceMu_smul
#print axioms KummerTheory.Decomposition.decompositionMap_surjective
#print axioms KummerTheory.Decomposition.decomposition_kummer
#print axioms KummerTheory.Decomposition.decomposition_kummerValue
#print axioms CoreReducedComparison.pullback_injective
#print axioms CoreReducedComparison.residue_classes_eq_of_specialization_squares