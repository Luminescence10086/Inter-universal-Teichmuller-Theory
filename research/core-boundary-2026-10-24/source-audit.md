# Core Kummer source audit

Parent note after validation: this document records the initial copy audit.
Two copied files were subsequently ported for Lean 4.34; their final bytes and
exact deltas are in port-manifest.json and upstream-port.patch. Do not interpret
the initial identical=true receipts as a statement that the current ports are
still byte-identical. The strict final compilation and editor evidence are
summarized in README.md; this mechanical note itself makes no Lean claim.

This is a source-provenance and interface note for four copied modules. No Lean command was run, so this note makes no compilation claim.

## Sources and provenance

- `Values.lean`, `Specialization.lean`, and `Decomposition.lean` are byte-for-byte copies from `research/core-kummer-2026-10-24/continuous-kummer-pin`, whose repository HEAD is `98b67dfe9c82415aa17caa633d93960b6829af2e`.
- `DecompositionSurjective.lean` is a byte-for-byte copy from `reviews/core-round/external/continuous-kummer-theory`, at exact HEAD `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa`.
- SHA-256 for all source and destination files is recorded in `source-files.json`. All four destinations were absent before this copy.
- The `Decomposition.lean` source at the newer external checkout had previously been checked byte-for-byte identical to the pin file (SHA-256 `b7a67da60e61998d631201b3053aadea387993c68984dd1e14a3f5d9d446b7a6`). The newer surjectivity proof is therefore being placed beside the pinned decomposition definitions without importing the external checkout as a whole.

## Imports

Direct imports in the copied files:

- `Values.lean`: `Kummer.Restriction`, `Kummer.Corestriction`.
- `Specialization.lean`: `Kummer.Values`.
- `Decomposition.lean`: `Kummer.Specialization`, `Mathlib.RingTheory.Valuation.RamificationGroup`.
- `DecompositionSurjective.lean`: `Kummer.Decomposition`, `Mathlib.RingTheory.Invariant.Profinite`.

The resulting source module chain is `DecompositionSurjective → Decomposition → Specialization → Values → (Restriction, Corestriction)`. `Restriction` imports `Equiv`; `Corestriction` imports `ContH1.Corestriction` and `Equiv`; `Equiv` imports `Basic`; `Basic` imports `ContH1.Basic` and `Hilbert90`. At the time of this copy, candidate `ContinuousKummerTheory` has `Basic`, `Equiv`, `ContH1.Basic`, and `Hilbert90`, but lacks `Restriction`, `Corestriction`, and `ContH1.Corestriction`; those required source modules were deliberately not copied under this task scope. Thus the direct import list of the new surjectivity file is only `Decomposition` plus Mathlib, but the four-file set is not a complete dependency closure in this candidate checkout. The source manifests for the pin and newer checkout both name Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` (v4.32.0). This supports compatibility at the dependency-version level, but does not establish that Lean elaborates the copied files in this candidate project.

## What the surjectivity theorem assumes

In `DecompositionSurjective.lean:506-509`, `decompositionMap_surjective` is proved under the inherited `Rational` section context and these theorem-level assumptions:

- `[IsAlgClosed Ω]`;
- `[Algebra.IsIntegral k (ResidueField A)]`;
- `hres : ∀ a : F, algebraMap F Ω a ∈ A → ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c`.

The inherited context (`:362-366`, `:430`) includes fields `k,F,Ω`, `k→F→Ω` algebra structures and scalar tower, valuation subring `A`, `hk : ∀ c : k, algebraMap k Ω c ∈ A`, compatible residue algebra structure `hkres`, and `[IsGalois F Ω]`. The intermediate `exists_decompositionMap_eq_of_fixes` (`:439-442`) has the same algebraic-closure and residue-integrality conditions and takes the explicit hypothesis that a residue-field automorphism fixes residues of every `a : F` whose image lies in `A`. Thus surjectivity is the rational-point case supplied by `hres`, not an unconditional theorem.

The decomposition map continuity used by the H¹ comparison is in `Decomposition.lean:107-108` and additionally needs `[Algebra.IsIntegral F Ω]`. `reduceMu` at `:143-150` is a monoid homomorphism (with `n ≠ 0`), and `reduceMu_smul` at `:163-170` proves equivariance; these declarations do not assert that `reduceMu` is injective, surjective, or an equivalence.

## Germ specialization and the weaker reflection route

The pinned IUT germ statement `reviews/core-round/external/iut/Iut/EtaleTheta/KummerClass.lean:173-182` has both sides in `H¹_cont(D_A, Mu n (ResidueField A))`:

- left: pull back from `Gal(Ω/F)` along the subgroup inclusion `D_A → Gal(Ω/F)`, and apply the coefficient homomorphism `reduceMu : Mu n Ω →* Mu n κ(A)`;
- right: pull back from `Gal(κ(A)/k)` along `decompositionMap : D_A → Gal(κ(A)/k)`, with coefficient map `MonoidHom.id` on the same residue coefficient group.

This follows the variance of `ContH1.map`: its group map is `H →* G`, and it sends `H¹_cont(G,M)` to `H¹_cont(H,N)` (`ContH1/Basic.lean:172-190`). The right side is therefore the pullback along `decompositionMap`; it can be called inflation only after identifying `D_A / ker(decompositionMap)` with `Gal(κ(A)/k)` and checking the quotient action. The new source proves the kernel is inertia (`Decomposition.lean:93-95`) and, under the rational-point hypotheses above, proves surjectivity, so that quotient description is available in principle. Do not reverse the group-map direction.

Suppose two source classes `C₁,C₂` have specialization identities `R(Cᵢ) = map(decompositionMap, id)(κ(aᵢ))`, where `R` is the combined restriction and coefficient-reduction map. If `R(C₁)=R(C₂)`, then the two right-hand pullbacks are equal. To deduce `κ(a₁)=κ(a₂)`, it suffices to reflect equality through `map(decompositionMap, id)`. `CoreCohomologyReflection.map_injective` can express this with `H=D_A`, `G=Gal(κ(A)/k)`, `M=N=Mu n κ(A)`, coefficient equivalence `MulEquiv.refl`, and the actual decomposition action; it requires continuity and surjectivity of `decompositionMap` plus the action compatibility. Equivalently, one may use injectivity of inflation after the quotient identification and compatible quotient action.

This route does not use injectivity or an inverse for `reduceMu`: the equality `R(C₁)=R(C₂)` is an input, and the conclusion is equality of residue-side Kummer classes. It does not imply `C₁=C₂` in `H¹_cont(Gal(Ω/F), Mu n Ω)`. That stronger conclusion would require a separate reflection result for `R`.

This is a mechanical source audit and conditional map argument; it does not claim that the hypotheses are instantiated for the original IUT comparison, nor that any IUT gap is resolved.


## Import-closure preparation

The three missing pin modules `Kummer/Restriction.lean`, `Kummer/Corestriction.lean`, and `ContH1/Corestriction.lean` were copied verbatim from the same pin commit and appended to `source-files.json` with source and destination SHA-256. Recursive inspection of all `import` declarations in the candidate `ContinuousKummerTheory` tree now finds each project module required by the seven requested checks: `ContH1.Corestriction`, `Kummer.Restriction`, `Kummer.Corestriction`, `Kummer.Values`, `Kummer.Specialization`, `Kummer.Decomposition`, and `Kummer.DecompositionSurjective`; external Mathlib imports are provided by the existing project Lake dependency. This confirms source-file import closure only, not successful elaboration.

`build-imports.ps1` records a fixed-order, one-file-per-process `lake env lean -DwarningAsError=true -o ...` sequence with separate logs, stops at the first failure, and writes `build-import-results.json` with per-module statuses/exit codes. The script was written but not run. The existing Lake configuration and prior build evidence were left untouched.
