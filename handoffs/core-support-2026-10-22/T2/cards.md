# T2 — Reusable declaration cards (STATIC_ONLY)

Task: `handoffs/core-support-2026-10-22.md`, section T2. Status: **STATIC_ONLY** everywhere.
Nothing here is machine-checked: no `lake build`, no `lean` run, no `#print`, no editor session.
Every "silently required" premise below is a **static reading** of the enclosing scope, not an
elaborator output. No premise is claimed to be satisfied by the original IUT; no proof is claimed
established.

Repo commits (all four verified `rev-parse HEAD`, `status --porcelain` empty):

| repo (under `reviews/core-round/external/`) | commit |
|---|---|
| `iut` | `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb` |
| `continuous-kummer-theory` | `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa` |
| `tate-curves-theta` | `d1fba94861c886b671f4137ab35e24b7474c9e00` |
| `local-class-field-theory` | `a6655a871f92138e486362f08f7df48204f3e985` |

No `INPUT_DRIFT`: all four HEADs equal the pinned commits and all four worktrees are clean.

Citation convention: `file:line` line numbers are those of the plain-text file as read from disk
(1-based, counting the license header). `file sha256` is over the whole file bytes.

---

## Card 1 — `Iut.Wall.EtaAlg` and its `realisation` field

- **Given name:** `Iut.Wall.EtaAlg` and its `realisation` field.
- **Real fully qualified name:** `Iut.Wall.EtaAlg`; field `Iut.Wall.EtaAlg.realisation`.
  The given name is **correct**.
- **Repo / commit:** `iut` @ `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`.
- **File / lines:** `reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean`, structure at
  **lines 96–125** (docstring 94–95, `structure` keyword 96, `realisation` field **123–125**).
- **File sha256:** `393ca2997810338b272b17ccdcc4690d819ff9fe4474fb47fe77ceb4e53fb05c` (229 lines).
- **Direct imports (the file's own `import` lines, 6–7):**
  `import Iut.Wall.Ind3`, `import Iut.MainTheorem`.
- **Kind:** `structure` (a `Type`-valued interface, not a proposition).

**Enclosing scope.** `namespace Iut` (83) → `namespace Wall` (85) → `open NumberField` (87);
`abbrev Pl (D : InitialThetaData.{0}) : Type := FinitePlace D.F ⊕ InfinitePlace D.F` (90);
then the section binder `variable (D : InitialThetaData.{0})` (**92**) — this is the only binder the
structure inherits, and it becomes an **explicit** parameter, so the real name is
`Iut.Wall.EtaAlg (D : InitialThetaData.{0})`. No typeclass binders and **no local instances** are in
scope at line 96.

`EtaAlg.lean:92` (the scope that supplies `D`):

```lean
variable (D : InitialThetaData.{0})
```

`EtaAlg.lean:94-125` (signature verbatim; docstring kept because it carries the field semantics):

```lean
/-- **The η-algorithm of [LANA], §9.1, as an interface** (see the module docstring for the
fields (T1)–(T3) and their sources). -/
structure EtaAlg where
  /-- The model étale-unit prime-strip `{G_v ↷ O^{×µ}_v}_v` (opaque). -/
  model : Pl D → GMData
  /-- The Hodge theaters (opaque; IUT I, `Θ^{±ell}NF`-Hodge theaters). -/
  Side : Type
  /-- There is a Hodge theater (IUT I). -/
  side_nonempty : Nonempty Side
  /-- The étale-unit BPS `B(H)` of a Hodge theater ([LANA], §4.2(c)). -/
  etUnit : Side → EtUnitBPS model
  /-- **The output** `LGP·S` of the η-algorithm, read in the concrete container ([LANA], §9.1,
  Steps 8–9; §6.2(i)), for a choice `ι` of an isomorphism of the input BPS `B` with the
  Θ-pilot BPS of a Hodge theater `h` (Step 1) and an (Ind3)-choice `S`. -/
  out : ∀ {B : BPS model D.bpsDegrees.bad} {h : Side},
    BPS.Iso B ⟨etUnit h, D.thetaValD⟩ → Ind3 D → Region D
  /-- **(T1)** (Ind1), (Ind2) — automorphisms of the étale-unit portion of the input — act on
  the (Ind3)-choices (IUT III, Theorem 3.11(i); [LANA], §10.4). -/
  ind12_acts_on_S : ∀ {B : BPS model D.bpsDegrees.bad} {h : Side} (α : EtUnitIso B.et B.et)
    (ι : BPS.Iso B ⟨etUnit h, D.thetaValD⟩), ∃ τ : Ind3 D ≃ Ind3 D, ∀ S,
      out ((BPS.Iso.mk α (ValBPS.Iso.refl _)).trans ι) S = out ι (τ S)
  /-- **(T2)** the output depends on the input only through its étale-unit portion and the
  étale-unit part of the choice ([LANA], Remark 6.2.2). -/
  etUnitOnly : ∃ f : ∀ {E : EtUnitBPS model} {h : Side}, EtUnitIso E (etUnit h) → Ind3 D →
      Region D, ∀ {B : BPS model D.bpsDegrees.bad} {h : Side}
      (ι : BPS.Iso B ⟨etUnit h, D.thetaValD⟩) (S : Ind3 D), out ι S = f ι.et S
  /-- **(T3) realisation**: every output is an adelic region in the holomorphic hull of a
  single (Ind1)-image of the concrete theta-pilot region (IUT III, Theorem 3.11(ii),
  Corollary 3.12; roadmap package P21). -/
  realisation : ∀ {B : BPS model D.bpsDegrees.bad} {h : Side}
    (ι : BPS.Iso B ⟨etUnit h, D.thetaValD⟩) (S : Ind3 D),
      IsAdelic D (out ι S) ∧ InHullOfImage D (out ι S)
```

**The `realisation` field alone** (`EtaAlg.lean:120-125`):

```lean
  /-- **(T3) realisation**: every output is an adelic region in the holomorphic hull of a
  single (Ind1)-image of the concrete theta-pilot region (IUT III, Theorem 3.11(ii),
  Corollary 3.12; roadmap package P21). -/
  realisation : ∀ {B : BPS model D.bpsDegrees.bad} {h : Side}
    (ι : BPS.Iso B ⟨etUnit h, D.thetaValD⟩) (S : Ind3 D),
      IsAdelic D (out ι S) ∧ InHullOfImage D (out ι S)
```

- **Explicit premises the declaration consumes:** the single explicit parameter
  `(D : InitialThetaData.{0})`. Inside the type, `side_nonempty : Nonempty Side` is itself a
  bundled existence premise (IUT I, Theorem A), not a hypothesis passed in from outside.
- **Output:** a structure *type*, not a proof. `realisation` is a field storing, for every input
  choice `(B, h, ι, S)`, a pair of propositions about the algorithm's output
  `out ι S : Region D`: `IsAdelic D (out ι S)` **and** `InHullOfImage D (out ι S)`.
- **Notes.** (i) The two conjuncts are *not* defined in this file; they come from
  `Iut.MainTheorem` (imported at line 7), so the strength of the card's conclusion is entirely
  determined there. (ii) `out` is a *field*, i.e. the η-algorithm is part of the data of an
  `EtaAlg`; this card therefore describes an interface, not an algorithm. (iii) The docstring
  (lines 29–56) states explicitly that the hull requirement is *weaker* than LANA's `InImage`,
  so an inhabitant of this structure is not LANA's algorithm.

---

## Card 2 — `Iut.Wall.EtaAlg.etaAnab_eq_etaQ_iff`

- **Given name:** `Iut.Wall.EtaAlg.etaAnab_eq_etaQ_iff`. **Correct** as given.
- **Repo / commit:** `iut` @ `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`.
- **File / lines:** `Iut/Wall/EtaAlg.lean`, theorem at **lines 151–153** (docstring 149–150).
- **File sha256:** `393ca2997810338b272b17ccdcc4690d819ff9fe4474fb47fe77ceb4e53fb05c`.
- **Direct imports:** `import Iut.Wall.Ind3` (6), `import Iut.MainTheorem` (7).
- **Kind:** `theorem` (an `↔`, i.e. `Iff`).

**Enclosing scope — this is where the card would be incomplete if only line 151 were quoted.**
`namespace Iut.Wall` (166 is the *close* of the earlier block; the theorem sits at 151, i.e. inside
the block opened at 85), then:

- `namespace EtaAlg` (**127**) — opens the namespace that the theorem name lives in.
- `variable {D} (A : EtaAlg D)` (**129**) — **redeclares `D` as implicit**, shadowing the
  explicit `variable (D : InitialThetaData.{0})` of line 92 for everything after line 129.
  Net effect on the elaborated type: `{D : InitialThetaData.{0}} → (A : EtaAlg D) → …`,
  i.e. `D` implicit, `A` explicit.
- `open NumberField` (87) is still in force.
- Declarations in the same scope that the statement immediately leans on: `abbrev BPSA` (132),
  `qBPS` (135), `thetaBPS` (138), `abbrev Choice (B : A.BPSA) (h : A.Side) :=
  BPS.Iso B (A.thetaBPS h)` (141), `etaAnab` (145–147).
- **No `local instance` and no typeclass binder** is in scope here.

`EtaAlg.lean:127-129` (the scope that supplies `A` and the implicit `D`):

```lean
namespace EtaAlg

variable {D} (A : EtaAlg D)
```

`EtaAlg.lean:149-153` (signature verbatim):

```lean
/-- **(9-1) for `(ι, S)` is an equation of real numbers**: `η^anab_{ι,S} = η_q` iff the output
has log-volume `−|log(q)|`. -/
theorem etaAnab_eq_etaQ_iff {h₁ h₂ : A.Side} (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D) :
    A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs :=
  ValBPS.eta_eq_eta_iff _ _ _
```

- **Explicit premises consumed:** `(A : EtaAlg D)` (from the section, explicit),
  `{h₁ h₂ : A.Side}` (implicit), `(ι : A.Choice (A.qBPS h₂) h₁)` (explicit),
  `(S : Ind3 D)` (explicit). **No propositional hypotheses** are consumed — the theorem
  introduces none and `hW`/`Wall` does not appear.
- **Output:** the biconditional
  `A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs`.
  Proof term is a single application of `ValBPS.eta_eq_eta_iff` (not one of the 8 cards).
- **Notes.** The name is honest: it is an `_iff`, and both sides are equations of real numbers
  (the left an equality of linear maps `B.val.C →ₗ[ℝ] ℝ`). The direction `→` is the one consumed
  by `exists_out_of_wall` (`EtaAlg.lean:195`), i.e. it converts the *wall equation* into the
  *log-volume value* without any additional hypothesis.

---

## Card 3 — `Iut.Wall.variant_of_wall`

- **Given name:** `Iut.Wall.variant_of_wall`. **Correct** as given (note the name is
  `Iut.Wall.variant_of_wall`, and `Wall` there is simultaneously a namespace and the `def Wall`
  of line 173).
- **Repo / commit:** `iut` @ `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`.
- **File / lines:** `Iut/Wall/EtaAlg.lean`, theorem at **lines 201–204** (docstring 197–200).
- **File sha256:** `393ca2997810338b272b17ccdcc4690d819ff9fe4474fb47fe77ceb4e53fb05c`.
- **Direct imports:** `import Iut.Wall.Ind3` (6), `import Iut.MainTheorem` (7).
- **Kind:** `theorem`.

**Enclosing scope — the file is not a single namespace block.** `end Wall` at 166 closes the
block that contains cards 1–2; then `open Wall in` (168) and `def Wall (D : InitialThetaData.{0})
(A : Wall.EtaAlg D) : Prop := …` (**173–175**) are stated in `namespace Iut` only; `namespace Wall`
is **reopened at 177**, where:

- `variable {D}` (**179**) — `D` implicit (again shadowing line 92's explicit version).
- `open NumberField` (87) still in force; `open Wall in` at 168 is *not* in force at 201.
- **No `local instance`**, no typeclass binder.
- In-scope declarations the theorem's statement/proof leans on: `def Wall` (173), `EtaAlg`
  (card 1), `EtaAlg.etaAnab` (145), `etaQ`, `Corollary312Variant`, `concreteVariantData`
  (from `Iut.MainTheorem`), `corollary312Variant_iff`, `logVol_le_rhs`,
  and `exists_out_of_wall` (189–195) — the latter is a **direct proof dependency that is not one
  of the 8 cards**.

`EtaAlg.lean:177-179` (the scope that supplies the implicit `D`):

```lean
namespace Wall

variable {D}
```

`EtaAlg.lean:201-204` (signature verbatim):

```lean
theorem variant_of_wall (A : EtaAlg D) (hW : Wall D A) :
    Corollary312Variant (concreteVariantData D) := by
  obtain ⟨U, hU, hI, hvol⟩ := exists_out_of_wall A hW
  exact (corollary312Variant_iff _).mpr (hvol ▸ logVol_le_rhs D hU hI)
```

- **Explicit premises consumed:** `(A : EtaAlg D)` and `(hW : Wall D A)` — i.e. the theorem is
  **hypothetical**: it consumes the wall hypothesis `Wall D A` (defined at 173 as
  `∀ h₁ h₂, BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂) → ∃ ι S, A.etaAnab ι S = etaQ D`).
  It does not assume `Wall`; it takes it as an argument. Nothing here asserts `Wall D A` holds.
- **Output:** `Corollary312Variant (concreteVariantData D)` — a `Prop`, the "variant" reading of
  IUT III Corollary 3.12 for the concrete variant data attached to `D`.
- **Notes.** (i) The proof goes through `exists_out_of_wall`, which consumes card 2
  (`(A.etaAnab_eq_etaQ_iff ι S).mp hη` at line 195) and the `realisation` field of card 1
  (line 194). Therefore **card 3 → card 2 is only a transitive relation**, not a direct one, and
  is deliberately **excluded** from `edges.csv`. (ii) The docstring names
  `Iut/Concrete/Ind1Invariance.lean` as the source of the `−|log(Θ)|` log-volume of the
  (Ind1)-image — a file not read for this task.

---

## Card 4 — `KummerTheory.restriction_kummer`

- **Given name:** `KummerTheory.restriction_kummer`. **Correct** as given.
- **Repo / commit:** `continuous-kummer-theory` @ `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa`.
- **File / lines:** `ContinuousKummerTheory/Kummer/Restriction.lean`, theorem at **lines 95–98**
  (docstring 93–94).
- **File sha256:** `a3cb72802180576ed19c3ea02a3f5118685969c66647789c5fa0bc6121fd395e` (123 lines).
- **Direct imports (line 6):** `import ContinuousKummerTheory.Kummer.Equiv`.
- **Kind:** `theorem`.

**Enclosing scope — quoting lines 95–98 alone is INCOMPLETE: it hides two section premises.**
`open groupCohomology IntermediateField` (23) → `namespace KummerTheory` (**25**), then:

- **27–29:** the master binder block
  `variable (K L ΩK ΩL : Type*) [Field K] [Field L] [Field ΩK] [Field ΩL] [Algebra K L]
  [Algebra K ΩK] [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL] [Algebra ΩK ΩL]
  [IsScalarTower K ΩK ΩL] [Normal K ΩK]`
  — all four base types **explicit**, plus 12 typeclass binders (incl. `Normal K ΩK`, needed for
  `Gal(ΩK/K)`, and both `IsScalarTower`s).
- **35:** `variable {K L ΩK ΩL}` — re-declares the four base types **implicit** from here on.
- **65:** `variable (n : ℕ)` — explicit section variable, in force at 95.
- **84:** `variable [Algebra.IsIntegral L ΩL]` — **an extra instance premise that appears nowhere
  in the quoted signature of lines 95–96**, yet is required at elaboration time because the
  statement uses `restriction`, whose definition (88–91) needs `continuous_galRestrict`
  (`[Algebra.IsIntegral L ΩL]` is a *binder of its own* at line 44) and is only available here
  because of this section variable.
- **No `local instance`** is declared in this file.

`Restriction.lean:27-29` and `65` and `84` (the scope that supplies the hidden arguments):

```lean
variable (K L ΩK ΩL : Type*) [Field K] [Field L] [Field ΩK] [Field ΩL]
  [Algebra K L] [Algebra K ΩK] [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL]
  [Algebra ΩK ΩL] [IsScalarTower K ΩK ΩL] [Normal K ΩK]
```

```lean
variable (n : ℕ)
```

```lean
variable [Algebra.IsIntegral L ΩL]
```

`Restriction.lean:93-98` (signature verbatim):

```lean
/-- **Kummer theory is compatible with restriction**: the restriction of the Kummer class of
`a ∈ Kˣ` is the Kummer class of the image of `a` in `Lˣ`. -/
theorem restriction_kummer [Algebra.IsIntegral K ΩK] [HasKummerRoots n K ΩK]
    [HasKummerRoots n L ΩL] (a : Kˣ) :
    restriction K L ΩK ΩL n (kummer n K ΩK a) =
      kummer n L ΩL (Units.map (algebraMap K L : K →* L) a) := by
```

- **Explicit premises consumed:** `[Algebra.IsIntegral K ΩK]`, `[HasKummerRoots n K ΩK]`,
  `[HasKummerRoots n L ΩL]` (declared on the theorem), `(a : Kˣ)`, `(n : ℕ)` (section, explicit),
  `(K L ΩK ΩL : Type*)` (section, implicit after line 35), and the 12 typeclass binders of 27–29.
  **Hidden/implicitly-consumed:** `[Algebra.IsIntegral L ΩL]` (line 84) — required by the
  `restriction` map occurring in the statement, though not printed on the theorem line.
- **Output:** the equation
  `restriction K L ΩK ΩL n (kummer n K ΩK a) =
   kummer n L ΩL (Units.map (algebraMap K L : K →* L) a)`,
  i.e. `res ∘ κ_K = κ_L ∘ (algebraMap-induced map on units)`.
- **Notes.** No finiteness of `L/K` is used (module docstring, lines 18–20). `Ω_K → Ω_L` is
  encoded as `[Algebra ΩK ΩL]` + `[IsScalarTower K ΩK ΩL]`; `[Normal K ΩK]` is present but the
  theorem does **not** require `IsGalois`. So this card is a statement about Kummer classes, not
  about any IUT-specific object.

---

## Card 5 — `KummerTheory.corestriction_kummer`

- **Given name:** `KummerTheory.corestriction_kummer`. **Correct** as given.
- **Repo / commit:** `continuous-kummer-theory` @ `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa`.
- **File / lines:** `ContinuousKummerTheory/Kummer/Corestriction.lean`, theorem at **lines 146–148**
  (docstring 145).
- **File sha256:** `363f9ca8e7ba6c6407e295f7b6aab745fb94a7c4ea0ecd18016ad5cc57f03144` (170 lines).
- **Direct imports (6–7):** `import ContinuousKummerTheory.ContH1.Corestriction`,
  `import ContinuousKummerTheory.Kummer.Equiv`.
- **Kind:** `theorem`.

**Enclosing scope — quoting lines 146–148 alone is INCOMPLETE: `L` here is not a field type but an
`IntermediateField`, and two section premises plus two section-local instances are hidden.**
`open groupCohomology IntermediateField ContH1` (29) → `namespace KummerTheory` (**31**), then:

- **33:** `variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)`
  — **`L` is an explicit `IntermediateField K Ω`**, not a field. (Contrast card 4, where `L` is a
  bare field type.) `K`, `Ω` implicit.
- **54:** `variable [IsGalois K Ω] [FiniteDimensional K L]` — **two instance premises not printed
  on the theorem line**; both are required because `corestriction` (142–143) depends on
  `index_range_galIncl` (57) via the section-local `FiniteIndex` instance.
- **60–61:** `instance : (galIncl L).range.FiniteIndex := ⟨by rw [index_range_galIncl]; exact
  Module.finrank_pos.ne'⟩` — **anonymous section-level instance** (a local instance in the
  `section`-scope sense), silently required downstream.
- **63:** `noncomputable instance : Fintype (Gal(Ω/K) ⧸ (galIncl L).range) := Fintype.ofFinite _`
  — second **anonymous section-level instance**; needed by `prod_corRep_eq_norm` (88), which the
  proof of card 5 uses.
- **138:** `variable (n : ℕ)` — explicit, in force at 146.
- **No named `local instance`** command is used, but the two anonymous `instance` declarations at
  60 and 63 behave as section-local instances for the whole remainder of the namespace.

`Corestriction.lean:33` and `54` (the scope that supplies `L` and the hidden instances):

```lean
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)
```

```lean
variable [IsGalois K Ω] [FiniteDimensional K L]
```

```lean
instance : (galIncl L).range.FiniteIndex :=
  ⟨by rw [index_range_galIncl]; exact Module.finrank_pos.ne'⟩

noncomputable instance : Fintype (Gal(Ω/K) ⧸ (galIncl L).range) := Fintype.ofFinite _
```

`Corestriction.lean:145-148` (signature verbatim):

```lean
/-- **Corestriction corresponds to the norm**: `cor (κ_L a) = κ_K (N_{L/K} a)`. -/
theorem corestriction_kummer [HasKummerRoots n K Ω] [HasKummerRoots n L Ω] (a : Lˣ) :
    corestriction L n (kummer n L Ω a) =
      kummer n K Ω (Units.map (Algebra.norm K : L →* K) a) := by
```

- **Explicit premises consumed:** `[HasKummerRoots n K Ω]`, `[HasKummerRoots n L Ω]`,
  `(a : Lˣ)` — note `Lˣ` is the unit group of the `IntermediateField`, `(n : ℕ)` (section,
  explicit), `(L : IntermediateField K Ω)` (section, explicit), `[Field K] [Field Ω]
  [Algebra K Ω]`. **Hidden/implicitly-consumed:** `[IsGalois K Ω]`, `[FiniteDimensional K L]`
  (line 54), plus the anonymous instances of lines 60 and 63.
- **Output:** `corestriction L n (kummer n L Ω a) =
  kummer n K Ω (Units.map (Algebra.norm K : L →* K) a)` — corestriction of a Kummer class is the
  Kummer class of the norm.
- **Notes.** This card is **finite-extension**-flavoured (`FiniteDimensional K L` is required,
  unlike card 4). **There is no direct relation between cards 4 and 5**: neither file imports the
  other, and neither statement/proof mentions the other's constant; the joint use happens in
  `ContinuousKummerTheory/Kummer/CorRes.lean:27` (`rw [restriction_kummer, corestriction_kummer,
  ← map_pow]`), which is not one of the 8 cards. `edges.csv` therefore contains **no 4↔5 row**.

---

## Card 6 — `KummerTheory.map_section_kummer_eq_kummerValue`

- **Given name:** `map_section_kummer_eq_kummerValue` (with the instruction to verify the fully
  qualified name). **Verification result:** the real fully qualified name is
  **`KummerTheory.map_section_kummer_eq_kummerValue`** — the bare name given in the handoff is
  **incomplete** (missing the `KummerTheory.` prefix, which lives in `namespace KummerTheory` at
  line 70). It **is** a `theorem`, and the `_eq_` is genuinely there. It is *not* a `lemma`.
- **Repo / commit:** `continuous-kummer-theory` @ `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa`.
- **File / lines:** `ContinuousKummerTheory/Kummer/Specialization.lean`, theorem at
  **lines 247–255** (`include hπ in` at **244**, docstring 245–246).
- **File sha256:** `a3852b0e12e7f0af7f87341f904df7914a32fd0b550f79bb0d4de4a3ec2a876a` (270 lines).
- **Direct imports (line 6):** `import ContinuousKummerTheory.Kummer.Values`.
- **Kind:** `theorem`, inside `section Values` (213–261) inside `namespace KummerTheory` (70).

**Enclosing scope — quoting lines 247–255 alone is INCOMPLETE in two ways: (a) the statement is
preceded by `include hπ in`, which forces `Continuous π` to be an explicit argument that does not
appear in the quoted type; (b) the argument list is dominated by 13 explicit section variables
declared 30 lines earlier.** Scope chain:

- `open groupCohomology` (42), `namespace ContH1` (44) … `end ContH1` (68),
  `namespace KummerTheory` (70), `open ContH1` (72).
- **74–75:** outer block `variable (n : ℕ) {Ω Ω' : Type*} [Field Ω] [Field Ω'] (B : Subring Ω)
  (hB : ∀ β : Ω, β ^ n ∈ B → β ∈ B) (ψ : B →+* Ω')` — this is where **`n : ℕ` (explicit)** comes
  from; it is used in the statement (`specMu n B hB ψ`, `kummer n F Ω`, `kummerValue n K ΩK x f`).
  The outer `B`, `hB`, `ψ` are **shadowed** by the ones re-declared at 219–221.
- **`section Values` (213)** re-declares, as one block spanning **215–223**:
  `{K F R Ω ΩK : Type*} [Field K] [Field F] [CommRing R] [Algebra K R] [Algebra R F]
  [Field Ω] [Field ΩK] [Algebra F Ω] [Algebra K ΩK] {D : Type*} [Group D]
  [MulDistribMulAction D (Mu n ΩK)] (ι : D →* Gal(Ω/F)) (π : D →* Gal(ΩK/K))
  (hDact : …) (B : Subring Ω) (hB : …) (hstab : …) (ψ : B →+* ΩK) (hψ : …)
  [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K ΩK] [HasKummerRoots n F Ω]
  [HasKummerRoots n K ΩK] [TopologicalSpace D] (hι : Continuous ι) (hπ : Continuous π)`
  — so `ι, π, hDact, B, hB, hstab, ψ, hψ, hι` are all **explicit** arguments of card 6, and
  `hπ` becomes one only because of the `include` on line 244.
- **No `local instance`** in this file's `section Values`; `include hB in` (88, 92) and
  `include hDact hψ in` (129) are analogous `include` directives, not instances.

`Specialization.lean:215-223` (the scope that supplies the argument list):

```lean
variable {K F R Ω ΩK : Type*} [Field K] [Field F] [CommRing R] [Algebra K R] [Algebra R F]
  [Field Ω] [Field ΩK] [Algebra F Ω] [Algebra K ΩK] {D : Type*} [Group D]
  [MulDistribMulAction D (Mu n ΩK)] (ι : D →* Gal(Ω/F)) (π : D →* Gal(ΩK/K))
  (hDact : ∀ (d : D) (ζ : Mu n ΩK), d • ζ = π d • ζ)
  (B : Subring Ω) (hB : ∀ β : Ω, β ^ n ∈ B → β ∈ B)
  (hstab : ∀ (d : D) (b : Ω), b ∈ B → ι d b ∈ B)
  (ψ : B →+* ΩK) (hψ : ∀ (d : D) (b : B), ψ ⟨ι d b, hstab d b b.2⟩ = π d (ψ b))
  [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K ΩK] [HasKummerRoots n F Ω]
  [HasKummerRoots n K ΩK] [TopologicalSpace D] (hι : Continuous ι) (hπ : Continuous π)
```

`Specialization.lean:244-255` (signature verbatim, **including** the `include hπ in` directive
because it changes the signature):

```lean
include hπ in
/-- Section form of `map_kummer_eq_map_kummerValue`: along a continuous section `s` of `π`, the
Kummer class of the function `f` restricts to the Kummer class `κ_K(f(x))` of its value. -/
theorem map_section_kummer_eq_kummerValue (s : Gal(ΩK/K) →* D) (hs : Continuous s)
    (hπs : ∀ g, π (s g) = g) (x : R →ₐ[K] K)
    (hRB : ∀ r : R, algebraMap F Ω (algebraMap R F r) ∈ B)
    (hψx : ∀ r : R, ψ ⟨_, hRB r⟩ = algebraMap K ΩK (x r)) (f : Rˣ) :
    ContH1.map s hs (MonoidHom.id _) continuous_id (fun g ζ => by rw [hDact, hπs]; rfl)
        (ContH1.map ι hι (specMu n B hB ψ) continuous_of_discreteTopology
          (specMu_smul n ι π hDact B hB hstab ψ hψ)
          (kummer n F Ω (Units.map (algebraMap R F : R →* F) f))) =
      kummerValue n K ΩK x f := by
```

- **Explicit premises consumed:** the 13 section arguments listed above
  (`n, ι, π, hDact, B, hB, hstab, ψ, hψ, hι`, and — via `include hπ` — `hπ`), plus the theorem's
  own `(s : Gal(ΩK/K) →* D)`, `(hs : Continuous s)`, `(hπs : ∀ g, π (s g) = g)`,
  `(x : R →ₐ[K] K)`, `(hRB : ∀ r : R, algebraMap F Ω (algebraMap R F r) ∈ B)`,
  `(hψx : …)` and `(f : Rˣ)`; plus the typeclass binders `[Field K] [Field F] [CommRing R]
  [Algebra K R] [Algebra R F] [Field Ω] [Field ΩK] [Algebra F Ω] [Algebra K ΩK] [Group D]
  [MulDistribMulAction D (Mu n ΩK)] [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K ΩK]
  [HasKummerRoots n F Ω] [HasKummerRoots n K ΩK] [TopologicalSpace D]`.
- **Hidden/silent:** `(hπ : Continuous π)` — **not in the quoted type**, injected by
  `include hπ in`. Without it the theorem would have no `hπ` argument; with it, callers must
  supply one.
- **Output:** the equation
  `s^*(ι^*(ψ_* κ_F(f))) = kummerValue n K ΩK x f` — the section-then-specialise pullback of the
  Kummer class of the *function* `f ∈ Rˣ` equals the Kummer class of its *value* `f(x)`.
- **Notes.** (i) `kummerValue n K ΩK x f` is definitionally `kummer` of `f(x)`
  (`KummerTheory.restriction_kummerValue` in `Kummer/Values.lean:87`); the proof of card 6 first
  rewrites `kummerValue_apply` and then defers to `map_section_kummer` — **not** to
  `restriction_kummer`. Hence **no direct edge to card 4 or card 5**, even though
  `Kummer/Values.lean` uses `restriction_kummer` internally (that is a transitive relation through
  a non-card file, and is excluded by the T2 scope rule).

---

## Card 7 — `TateCurvesTheta.TateParameter.restriction_kummer_thetaUnit`

- **Given name:** `restriction_kummer_thetaUnit` (with the instruction to verify the fully
  qualified name). **Verification result — the handoff is materially inaccurate here.**
  The declaration is **not** in `continuous-kummer-theory` and is **not** in namespace
  `KummerTheory`. Its real fully qualified name is
  **`TateCurvesTheta.TateParameter.restriction_kummer_thetaUnit`**, and it lives in the
  **`tate-curves-theta`** repository. Evidence: `git grep -F 'restriction_kummer_thetaUnit'`
  in `continuous-kummer-theory` exits **1** (absent); the same grep in `tate-curves-theta` exits
  **0**. It is a `theorem`, and the `_eq_` form in the handoff's name is right in spirit but the
  name as printed matches only the *unqualified* suffix.
- **Repo / commit:** `tate-curves-theta` @ `d1fba94861c886b671f4137ab35e24b7474c9e00`.
- **File / lines:** `TateCurvesTheta/Kummer/ThetaValues.lean`, theorem at **lines 284–287**
  (docstring 281–283).
- **File sha256:** `eca16ee96c794c002219a7d36e51f1ed6358dcea7757a87fab3a27330a6650f5` (293 lines).
- **Direct imports (6–10):** `import ContinuousKummerTheory.Kummer.ZHat`,
  `import ContinuousKummerTheory.Kummer.Restriction`, `import TateCurvesTheta.Theta.Durfee`,
  `import TateCurvesTheta.Theta.Inversion`, `import TateCurvesTheta.QParameter.BaseChange`.
  **The second of these is the direct import edge to card 4.**
- **Kind:** `theorem`, inside `noncomputable section` (48), `namespace TateCurvesTheta` (52),
  `namespace TateParameter` (54), `section BaseChange` (248–289).

**Enclosing scope — the whole `section BaseChange` binder block is required to read this card.**
- **48:** `noncomputable section` — every declaration in the file is `noncomputable`.
- `open KummerTheory` (**50**) — this is why `restriction`, `kummer` resolve unqualified.
- **56:** `variable {K : Type*} [NormedField K] (t : TateParameter K)` — `t` explicit,
  `K` implicit, `[NormedField K]` from the section.
- **248:** `section BaseChange`; **250:** `variable [CompleteSpace K] [IsUltrametricDist K]
  (L : Type*) [NormedField L] [NormedAlgebra K L]` — **`[CompleteSpace K]`,
  `[IsUltrametricDist K]` are instance premises not printed on the theorem line**, required by
  `algebraMap_theta` (254) and hence by `theta_baseChange_ne_zero` (264) used in the statement.
- **276–279:** `variable (n : ℕ) (ΩK ΩL : Type*) [Field ΩK] [Field ΩL] [Algebra K ΩK]
  [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL] [Algebra ΩK ΩL]
  [IsScalarTower K ΩK ΩL] [Normal K ΩK] [Algebra.IsIntegral K ΩK] [Algebra.IsIntegral L ΩL]
  [HasKummerRoots n K ΩK] [HasKummerRoots n L ΩL]`
  — note `[Algebra.IsIntegral L ΩL]` at 278 is **exactly** the premise that card 4 hides at
  `Restriction.lean:84`; here it is supplied explicitly.
- **No `local instance`** in scope.

`ThetaValues.lean:250` and `276-279` (the scope that supplies the hidden instance premises):

```lean
variable [CompleteSpace K] [IsUltrametricDist K] (L : Type*) [NormedField L] [NormedAlgebra K L]
```

```lean
variable (n : ℕ) (ΩK ΩL : Type*) [Field ΩK] [Field ΩL] [Algebra K ΩK] [Algebra L ΩL]
  [Algebra K ΩL] [IsScalarTower K L ΩL] [Algebra ΩK ΩL] [IsScalarTower K ΩK ΩL] [Normal K ΩK]
  [Algebra.IsIntegral K ΩK] [Algebra.IsIntegral L ΩL] [HasKummerRoots n K ΩK]
  [HasKummerRoots n L ΩL]
```

`ThetaValues.lean:281-287` (signature verbatim):

```lean
/-- **Restriction of Kummer classes of theta values**: the restriction to `Gal(Ω_L/L)` of
`κ_K(θ(u))` is the Kummer class over `L` of the theta value of the base-changed Tate parameter
at the image of `u`. -/
theorem restriction_kummer_thetaUnit (u : Kˣ) (hu : t.theta u ≠ 0) :
    restriction K L ΩK ΩL n (kummer n K ΩK (t.thetaUnit u hu)) =
      kummer n L ΩL ((t.baseChange L).thetaUnit _ (t.theta_baseChange_ne_zero L u hu)) := by
  rw [restriction_kummer, map_thetaUnit]
```

- **Explicit premises consumed:** `(t : TateParameter K)` (section, explicit),
  `(u : Kˣ)`, `(hu : t.theta u ≠ 0)` (declared on the theorem), `(L : Type*)`,
  `(n : ℕ)`, `(ΩK ΩL : Type*)` (section, explicit); typeclass premises
  `[NormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]`
  and the 15 binders of 276–279.
- **Output:** `restriction K L ΩK ΩL n (kummer n K ΩK (t.thetaUnit u hu)) =
  kummer n L ΩL ((t.baseChange L).thetaUnit _ (t.theta_baseChange_ne_zero L u hu))`.
- **Notes.** (i) The proof is **one rewrite with card 4 plus `map_thetaUnit`**: this is a genuine
  **direct `proof_reference` edge to card 4** (`ThetaValues.lean:287`), in addition to the direct
  file-level import (`ThetaValues.lean:7`). (ii) The wildcard `_` in the right-hand
  `thetaUnit`'s nonzero proof is supplied by `t.theta_baseChange_ne_zero L u hu`. (iii) This card
  carries the value `t.baseChange L` (base-changed Tate parameter), not `t`.

---

## Card 8 — `PadicField.eq_artin_of_forall`

- **Given name:** `PadicField.eq_artin_of_forall`. **Correct** as given.
- **Repo / commit:** `local-class-field-theory` @ `a6655a871f92138e486362f08f7df48204f3e985`.
- **File / lines:** `LocalClassFieldTheory/Reciprocity/ArtinUnique.lean`, theorem at
  **lines 153–159** (`include hp in` at **149**, docstring 150–152).
- **File sha256:** `0d0221fea075835788dd31e92859a69536b404cee91761ee1d41fb1917af5247` (172 lines).
- **Direct imports (line 6):** `import LocalClassFieldTheory.Reciprocity.ArtinInertia`.
- **Kind:** `theorem`.

**Enclosing scope — two file-level settings silently change what the signature means.**
- **28:** `set_option linter.unusedSectionVars false` — **the whole file suppresses the unused
  section variable linter**, so an in-scope section variable may be absent from a declaration
  without any warning. This is precisely the circumstance in which a card built from the
  `theorem` line alone goes wrong; treat the 34–37 block as authoritative, not the theorem line.
- **30:** `open IntermediateField`; **32:** `namespace PadicField` (32–172).
- **34:** `variable {p : ℕ} [hp : Fact p.Prime]` — `p` implicit;
  `hp : Fact p.Prime` is an **instance-implicit section variable**.
- **35:** `variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]`.
- **36–37:** `variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
  [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω]`.
- **149:** `include hp in` — **forces the `Fact p.Prime` instance to be an argument** of
  `eq_artin_of_forall`, although the printed statement never mentions `hp`. (The same directive is
  used at 66 and 161 for the neighbouring lemmas.)
- **No `local instance`** is declared in this file.

`ArtinUnique.lean:28` and `34-37` (the scope and the linter setting):

```lean
set_option linter.unusedSectionVars false
```

```lean
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]
```

`ArtinUnique.lean:149-159` (signature verbatim, including `include hp in`):

```lean
include hp in
/-- **Characterisation of the Artin map**: a homomorphism `r : Kˣ → Gal(K^ab/K)` sending
uniformisers to Frobenius elements and norms from each finite abelian `L` into `Gal(K^ab/L)` is
the Artin map. -/
theorem eq_artin_of_forall (r : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω))
    (hr : ∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
      (r x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K)
    (hrN : ∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
      r x y = y) : r = artin p K Ω :=
  eq_of_frob_of_norm r _ hr (fun x hx _ hn y hy ↦ artin_apply_of_pow_eq x hx hn y hy) hrN
    artin_apply_of_mem_normGroup
```

- **Explicit premises consumed:** `(r : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω))`,
  the Frobenius clause
  `(hr : ∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
   (r x ⟨y, …⟩ : Ω) = y ^ q p K)`,
  and the norm clause
  `(hrN : ∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
   r x y = y)`.
  Plus the typeclass context `[Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Field Ω]
  [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω]` and, via
  `include hp`, `[Fact p.Prime]`.
- **Output:** `r = artin p K Ω` — uniqueness/characterisation: any `r` with the Frobenius and
  norm-clause properties equals the Artin map.
- **Notes.** (i) This card has **no relation to any of cards 1–7**: different repository, no
  import path between them, no shared constant. (ii) `eq_artin_iff` (161–167) is the packaged
  form and is **not** a separate card. (iii) `eq_of_frob_of_norm` — the real workhorse — is
  earlier in the same file and is not one of the 8 cards. (iv) Because of the `set_option` at 28,
  nothing should be concluded from the *absence* of a section variable in this file's signatures.

---

## `edges.csv` semantics

Direction: **`from` = the card that carries the reference, `to` = the card being referenced**
(i.e. `from` depends on `to`). Kinds:

- `import` — the file of `from` has a direct `import` line for the file of `to`.
- `signature_reference` — the *type* of `from` mentions a declaration of `to`.
- `proof_reference` — the *proof term* of `from` invokes a declaration of `to`.

Only the following are counted: the 4 rows listed in `edges.csv` (2 `signature_reference`,
1 `import`, 1 `proof_reference`). Explicitly **excluded** because they are only transitive or
involve non-card files: card 3 → card 2 (through `exists_out_of_wall`); card 6 → cards 4/5
(through `Kummer/Values.lean`); cards 4 ↔ 5 (jointly used only in `Kummer/CorRes.lean`); every
relation passing through `Iut.Wall.Ind3`, `Iut.MainTheorem`, `Kummer.Equiv`,
`ContH1.Corestriction`, `TateCurvesTheta.QParameter.BaseChange` or
`LocalClassFieldTheory.Reciprocity.ArtinInertia`. Card 8 is isolated.
