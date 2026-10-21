# p-adic / log / Kummer feasibility inventory

**Question.** What does the *pinned* Mathlib already give us for an IUT-style semantic bridge
(a `ℚ_p^×`-decomposition + `p`-adic logarithm + Kummer/ramification scaffolding), and what would
have to be proved from scratch?

**Answer in one line.** Items 1, 2 (residue-field half) and 5 are essentially *there*, item 2's
Teichmüller half is *one Hensel application away*, item 4 is *generic field theory only*, and
item 3 (the `p`-adic logarithm) is **absent**, with roughly half of its supporting lemmas present
and the series-level API missing.

- Pinned environment: Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib commit
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`
  (`C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib`, oleans present, 8370 `.lean` files
  under `Mathlib/`).
- Worktree: `D:\iut-wt\x-feas` on branch `explore/feas`. The main checkout was **read only**.
- Verdicts below use three grades only: **exists** (usable now, exact name), **partial**
  (ingredients present, named gap list follows), **absent** (no name; grep + `#check` both negative).

## Method (reproducible)

```
# greps: ripgrep over C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib/Mathlib/**
# probes (reads only; no `-o`, so no olean is written and the main checkout is untouched):
cd 'D:\Inter-universal Teichmüller Theory\bridge'
lake env lean --json 'D:\iut-wt\x-feas\research\exploration\probe-padic-inventory-round1.lean'
lake env lean --json '.../probe-padic-inventory-round2.lean'
lake env lean --json '.../probe-padic-inventory-round3.lean'
lake env lean --json '.../probe-padic-inventory-round4.lean'
```

Never run: `lake build`, any write into the main checkout, any edit of Lean sources. No `sorry`,
no axiom, no proof attempt: the probes are `#check` / `#synth`-grade only.

Probe transcripts: `probe-round{1,2,3,4}-digest.txt` (line-numbered, so every claim below can be
traced to one `#check` line). `EXIT=1` on every round is expected — it is produced by the
deliberately-absent names (`Padic.log`, `KummerTheory`, …).

---

## 1. Summary table

| # | Item | Verdict | Exact identifiers that do the work | Cheapest evidence |
|---|------|---------|-----------------------------------|-------------------|
| 1 | `ℚ_p^× ≅ ℤ × ℤ_[p]^×` + `Valued`/`WithVal`/`ValuativeRel`/`Multiplicative ℤ` | **partial** (elementwise ✓, bundled ✗) | `PadicInt.unitCoeff`, `PadicInt.unitCoeff_spec`, `Padic.valuation_mul`, `Padic.mulValuation`, `ValuativeRel`, `WithVal.equiv`, `Padic.withValRingEquiv`, `HeightOneSpectrum.valuationOfNeZero` | `PadicIntegers.lean:407,417`; probes r1 L42–L57 |
| 2 | `ℤ_p^×` structure: `(1+pℤ_p)` × roots of unity (Teichmüller), residue field, `ZMod` reduction, norm/ideal layers | **partial** (residue half ✓, Teichmüller ✗) | `PadicInt.residueField`, `PadicInt.toZMod`, `PadicInt.ker_toZMod`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `IsLocalRing.surjective_units_map_of_local_ringHom`, `ValuationSubring.principalUnitGroup`, `ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits` | `RingHoms.lean:349`; `PadicIntegers.lean:470`; probes r1 L67–L97 |
| 3 | `p`-adic `log`/`exp`/`Lubin–Tate` | **absent** (nothing at all); convergence kit **partial** | have: `PadicInt.dividedPowers`, `Padic.nonarchimedean`, `padicValNat_factorial_lt_of_ne_zero`, `padicValNat_le_nat_log`, `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, `HasSummableGeomSeries ℚ_[p]`, `CompleteSpace ℚ_[p]` | `DividedPowers/Padic.lean:139`; probes r1 L101–L126, r2 L32–L36 |
| 4 | Kummer theory for local fields | **partial** (general field theory only) | `isCyclic_tfae`, `autEquivRootsOfUnity`, `autEquivZmod`, `X_pow_sub_C_irreducible_iff_of_odd`, `rootsOfUnity`; `IsDedekindDomain.selmerGroup` machinery | `FieldTheory/KummerExtension.lean:555,390,423`; probes r1 L130–L139 |
| 5 | Ramification / filtration + ramified-extension normalization | **exists** (rich), with two naming traps | `Ideal.ramificationIdx`, `Ideal.ramificationIdx'`, `Ideal.ramificationIdxIn`, `Ideal.inertiaDeg`, `IsDiscreteValuationRing.addVal`, `IsDiscreteValuationRing.idealOrderIsoENat`, `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` | `RingTheory/RamificationInertia/Ramification.lean:52`; `NumberTheory/RamificationInertia/Valuation.lean:57` |

`partial` is *not* a hedge: every row marked partial is followed by §4's explicit gap list, and
the distinction between "name missing" and "concept missing" was probed separately (e.g.
`NonarchimedeanRing ℚ_[p]` fails `#synth`, while `Valued ℚ_[p]` has no instance but is one line of
`NormedField.toValued`).

---

## 2. Item-by-item evidence

### 2.1 Item 1 — the valuation decomposition

**What exists (and where).**

| Identifier | File:line | Statement (abridged) |
|---|---|---|
| `Padic.valuation` | `PadicNumbers.lean:1035` | `ℚ_[p] → ℤ` |
| `Padic.norm_eq_zpow_neg_valuation` | `PadicNumbers.lean:1048` | `x ≠ 0 → ‖x‖ = p ^ (-x.valuation)` |
| `Padic.norm_eq_zpow_log_mulValuation` | `PadicNumbers.lean:1197` | `x ≠ 0 → ‖x‖ = p ^ (mulValuation x).log` |
| `Padic.valuation_mul` | `PadicNumbers.lean:1101` | `x ≠ 0 → y ≠ 0 → (x*y).valuation = x.valuation + y.valuation` |
| `Padic.valuation_inv` | `PadicNumbers.lean:1111` | `(x⁻¹).valuation = -x.valuation` |
| `Padic.valuation_p` | `PadicNumbers.lean:1086` | `(p : ℚ_[p]).valuation = 1` |
| `Padic.mulValuation` | `PadicNumbers.lean:1177` | `Valuation ℚ_[p] ℤᵐ⁰` (i.e. `WithZero (Multiplicative ℤ)`) |
| `Padic.addValuation` | `PadicNumbers.lean:1202` | `AddValuation ℚ_[p] (WithTop ℤ)` |
| `PadicInt.valuation` | `PadicIntegers.lean:324` | `ℤ_[p] → ℕ` |
| `PadicInt.unitCoeff` | `PadicIntegers.lean:407` | `{x : ℤ_[p]} → x ≠ 0 → ℤ_[p]ˣ` |
| `PadicInt.unitCoeff_spec` | `PadicIntegers.lean:417` | `x = ↑(unitCoeff hx) * ↑p ^ x.valuation` |
| `PadicInt.mkUnits` / `norm_units` / `isUnit_iff` | `PadicIntegers.lean:393,403,370` | `‖u‖ = 1 → ℤ_[p]ˣ`; `‖(u:ℤ_[p])‖ = 1`; `IsUnit z ↔ ‖z‖ = 1` |
| `ValuativeRel`, `ValuativeRel.valuation` | `Topology/…/ValuativeRel/Basic.lean`; instance for `ℚ_[p]` at `Padics/ValuativeRel.lean:29` | `ValuativeRel ℚ_[p]` **is** an instance (`Padic.instValuativeRel`, r1 L93) |
| `Valued`, `WithVal`, `WithVal.equiv` | `Topology/Algebra/Valued/{Defs,WithVal}.lean:156` | `WithVal v ≃+* R` |
| `Padic.withValRingEquiv` | `Padics/WithVal.lean:106` | `(Rat.padicValuation p).Completion ≃+* ℚ_[p]` |
| `PadicInt.withValIntegersRingEquiv` | `Padics/WithVal.lean:200` | `𝒪[(Rat.padicValuation p).Completion] ≃+* ℤ_[p]` |
| `HeightOneSpectrum.withValEquiv` | `Padics/HeightOneSpectrum.lean:140` | `WithVal … ≃+* …` |
| `Multiplicative`, `Multiplicative.ofAdd` | r1 L55–L56 | plain type tags (no p-adic-specific lemma) |
| `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` | `DedekindDomain/SelmerGroup.lean:109` | `Kˣ →* Multiplicative ℤ` — **the only bundled `ℤ`-valued unit valuation in Mathlib**, but for a Dedekind domain's fraction field (so `ℚ`, not `ℚ_[p]`) |
| `valuationOfNeZeroMod` / `valuation_of_unit_eq` | ibid.:135, 121 | modulo `n`-th powers; `Rˣ ↦ 1` |
| `ValuationSubring.unitGroup`, `unitGroupMulEquiv` | `ValuationSubring.lean:496,503` | `Subgroup Kˣ`, `A.unitGroup ≃* Aˣ` |

**What is absent.** There is **no bundled monoid isomorphism** `ℚ_[p]ˣ ≃* Multiplicative ℤ × ℤ_[p]ˣ`.
Grep for `≃*`/`≃+*` inside `Mathlib/NumberTheory/Padics/**` returns exactly five hits, all unrelated
(`Rat.IsIntegralClosure.intEquiv`, `mahlerEquiv`, `Padic.withValRingEquiv`,
`PadicInt.withValIntegersRingEquiv`, `toCLMEquiv`). Probes for `Padic.unitsEquiv`,
`PadicInt.unitBall`, `Padic.valued` are all `Unknown constant` (r1 L61–L63).

Two traps worth recording:

- `PadicInt.unitBall` **does not exist**, but that is not a gap: `ℤ_[p]` *is* the closed unit ball
  (`Mathlib` defines `PadicInt p := {x : ℚ_[p] // ‖x‖ ≤ 1}`, `PadicIntegers.lean:60`), and the
  generic ball-subsemigroup is `Subsemigroup.unitBall` (`Analysis/Normed/Field/UnitBall.lean:32`,
  `‖x‖ < 1`, i.e. the *open* ball — a different object).
- `Valued ℚ_[p]` is **not** an instance (r2 L32) but is obtainable in one line from
  `NormedField.toValued : [NormedField K] → [IsUltrametricDist K] → Valued K NNReal` (r3 L15);
  `#synth NormedField ℚ_[p]` succeeds (`Padic.normedField`, r1 L95). So "no `Valued` instance" is a
  convenience gap, not a mathematical one. Do **not** budget for it.

### 2.2 Item 2 — `ℤ_p^×` structure

**Residue half — exists.**

| Identifier | File:line | Statement |
|---|---|---|
| `PadicInt.residueField` | `RingHoms.lean:349` | `IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p` |
| `PadicInt.toZMod` / `ker_toZMod` | `RingHoms.lean:300, 327` | `ℤ_[p] →+* ZMod p`; `ker = maximalIdeal ℤ_[p]` |
| `PadicInt.toZModPow` / `ker_toZModPow` | `RingHoms.lean:447, 459` | `ℤ_[p] →+* ZMod (p^n)`; `ker = span {p^n}` |
| `PadicInt.zmodRepr_units_ne_zero` | `RingHoms.lean:260` | units survive reduction |
| `PadicInt.norm_le_pow_iff_mem_span_pow` | `PadicIntegers.lean:470` | `‖x‖ ≤ p^(-n) ↔ x ∈ span {p^n}` |
| `PadicInt.norm_le_pow_iff_le_valuation` | `PadicIntegers.lean:452` | `x ≠ 0 → (‖x‖ ≤ p^(-n) ↔ n ≤ x.valuation)` |
| `PadicInt.mem_span_pow_iff_le_valuation` | `PadicIntegers.lean:457` | `x ≠ 0 → (x ∈ span {p^n} ↔ n ≤ x.valuation)` |
| `PadicInt.maximalIdeal_eq_span_p` | `PadicIntegers.lean:510` | `maximalIdeal ℤ_[p] = span {p}` |
| instances | `#synth` r1 L91–L97 | `IsDiscreteValuationRing ℤ_[p]`, `IsLocalRing ℤ_[p]`, `ValuationRing ℤ_[p]` all fire |

Note the asymmetry in the second column of `norm_le_pow_iff_mem_span_pow`: the RHS is a *natural*
power of the ideal while the LHS is a *negative* `ℤ` exponent. `Filtration.lean` already relies on
exactly this form (`local-field/LocalFieldAudit/Filtration.lean:66–76`), so the existing
audit's base-field layer is on solid ground.

**The `(1+p)`-quotient — exists generically.**

| Identifier | File:line | Statement |
|---|---|---|
| `ValuationSubring.principalUnitGroup` | `ValuationSubring.lean:638` | `Subgroup Kˣ` |
| `ValuationSubring.principalUnitGroupEquiv` | `ValuationSubring.lean:704` | `A.principalUnitGroup ≃* ker (residue on units)` |
| `ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits` | `ValuationSubring.lean:749` | `A.unitGroup ⧸ principalUnitGroup ≃* (ResidueField A)ˣ` |
| `IsLocalRing.surjective_units_map_of_local_ringHom` | (probe r1 L78, r4 L8) | `Surjective f → IsLocalHom f → Surjective (Units.map f)` |

`unitsModPrincipalUnitsEquivResidueFieldUnits` is *literally* "`𝓞^×/(1+𝔭) ≅ κ^×`" — for an
arbitrary `ValuationSubring`. But there is **no `ValuationSubring ℚ_[p]` instance/definition for
`ℤ_[p]`** (grep: `ValuationSubring ℤ_[p]` has zero hits; the analogue exists only for `ℂ_[p]` as
`PadicComplexInt`, `Padics/Complex.lean:251`). The cheap substitute is
`IsLocalRing.surjective_units_map_of_local_ringHom PadicInt.toZMod` + `ZMod.ringHom_surjective`,
which gives surjectivity `ℤ_[p]ˣ ↠ (ZMod p)ˣ` with no `ValuationSubring` at all.

**Teichmüller half — absent.** This is the sharpest negative result in this report:

- `Mathlib/NumberTheory/Padics/**` contains **zero** occurrences of `rootsOfUnity`,
  `IsPrimitiveRoot`, `X_pow_sub`, `nthRoots` (grep, whole directory).
- `PadicInt.teichmuller`, `Padic.rootsOfUnity` are `Unknown constant` (r1 L89, r2 L70).
- The only Teichmüller maps in Mathlib are `WittVector.teichmuller : R →* 𝕎 R`
  (`RingTheory/WittVector/Teichmuller.lean:93`) and `Perfection.teichmuller : Perfection (R⧸I) p →* R`
  (`RingTheory/Teichmuller.lean:101`) — both correct and available (r2 L65–L66), but neither comes
  with `𝕎(𝔽_p) ≅ ℤ_p`, so neither *directly* yields Teichmüller representatives in `ℤ_[p]`.
- Closest existing contact between `ℤ_[p]ˣ` and root-of-unity behaviour: the cyclotomic character
  `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ` and the congruence
  `modularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow`
  (`NumberTheory/Cyclotomic/CyclotomicCharacter.lean:307, 101`) — a *target* use of `ℤ_[p]ˣ`, not a
  source of `μ_{p-1}(ℤ_p)`.
- The raw material for Teichmüller **is** present: `hensels_lemma` (root-namespace, note the
  import `Mathlib.NumberTheory.Padics.Hensel`; `Hensel.lean:462`, quoted in full at probe r4 L5)
  with the uniqueness clause, and `IsCyclic (ZMod p)ˣ` + `IsCyclic.exists_generator`
  (`RingTheory/ZMod/UnitsCyclic.lean:77`, r3 L31).

### 2.3 Item 3 — `p`-adic logarithm

**Absent, unambiguously.** `Padic.log`, `Padic.exp`, `PadicInt.log`, `PadicInt.exp`, `Padic.logP`,
`LubinTate` are all `Unknown constant / Unknown identifier` (r1 L101–L106). There is no `Log.lean`,
no `Exp.lean`, no `LubinTate.lean` anywhere in the tree; grep over all of `Mathlib` for
`padicLog|PadicLog|logSeries|LubinTate` returns nothing p-adic (only the real/complex `expSeries`).
The previous round's finding is confirmed and now explained: the names are missing because the
theory is missing, not because they were renamed.

**What the standard proof needs, and what is already there.** The reference proof of
`log(1+x) = ∑ (-1)^{n+1} x^n/n` on `‖x‖ < 1` needs (a) `x^n/n → 0`, (b) a `HasSum` for the series,
(c) multiplicativity via a double-series rearrangement, (d) injectivity onto the principal units.

| Ingredient | Available? | Identifier |
|---|---|---|
| `n!`/`n` p-adic valuation bound | **yes** | `padicValNat_factorial_lt_of_ne_zero` (`PadicVal/Basic.lean:641`), `padicValNat_le_nat_log` (`:509`), `padicValNat_factorial` (`:615`) |
| `x^n/n! ∈ ℤ_[p]` for `x ∈ pℤ_p` (integrality) | **yes** | `PadicInt.dividedPowers : DividedPowers (span {p})` (`RingTheory/DividedPowers/Padic.lean:139`) — this is precisely "the divided-power structure = `x^n/n!` stays integral" |
| ultrametric inequality | **yes** | `Padic.nonarchimedean` (`PadicNumbers.lean:834`), `PadicInt.nonarchimedean` (`PadicIntegers.lean:215`), `PadicInt.norm_add_eq_max_of_ne` (`:217`) |
| strict-triangle/`≤ p^n ↔ < p^{n+1}` layer calculus | **yes** | `Padic.norm_le_pow_iff_norm_lt_pow_add_one` (`PadicNumbers.lean:1216`), `Padic.norm_p_zpow` |
| nonarchimedean `Summable`/`HasSum` criterion | **yes** | `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (`Topology/Algebra/InfiniteSum/Nonarchimedean.lean:101/104`), `NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one` (`:104`) |
| tails → 0 | **yes** | `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `CompleteSpace ℚ_[p]` (`Padic.instCompleteSpace`, r1 L126) |
| geometric series | **yes** | `HasSummableGeomSeries ℚ_[p]` fires (r2 L34); `hasSum_geometric_of_norm_lt_one` |
| **product of two `HasSum`s** (for multiplicativity) | **blocked** | `HasSum.mul_of_nonarchimedean` (`Nonarchimedean.lean:126`) needs `NonarchimedeanRing R`; `#synth NonarchimedeanRing ℚ_[p]` and `#synth NonarchimedeanRing ℤ_[p]` both **fail** (r2 L36–L37). `NonarchimedeanAddGroup ℚ_[p]` does fire (via `IsUltrametricDist.nonarchimedeanAddGroup`, r2 L35), so only the ring class is missing. |
| `NormedSpace.exp` usable | **no** | `NormedSpace.exp` typechecks as a bare function (`[Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] → 𝔸 → 𝔸`, r1 L122) but its entire theory needs `NormedAlgebra ℚ 𝔸` (`expSeries_div_hasSum_exp`, r1 L123) and `#synth NormedAlgebra ℚ ℚ_[p]` **fails** (r2 L33) — necessarily, since `NormedAlgebra ℚ` forces the *archimedean* norm on `ℚ`. So `NormedSpace.exp` is a dead end for `ℚ_[p]`; do not budget around it. |
| binomial coefficients divisible by p | **yes** | `padicValNat_choose` (`PadicVal/Basic.lean:660`, the digit-sum formula), `Nat.Prime.dvd_choose_pow` (r2 L76) |
| Lubin–Tate formal group | **no** | no declaration in the tree |

So roughly: all *scalar* arithmetic inputs exist; the *series-level* layer does not, and one type
class (`NonarchimedeanRing ℚ_[p]`) is the gate for the one rearrangement lemma the multiplicativity
proof needs.

### 2.4 Item 4 — Kummer theory

**Generic field theory — exists and is substantial** (`Mathlib/FieldTheory/KummerExtension.lean`):

| Identifier | File:line | Statement (abridged) |
|---|---|---|
| `isCyclic_tfae` | `:555` | `μ_n ⊆ K`, `[L:K] = n` ⟹ TFAE: (`IsGalois` + `IsCyclic`) / (`L` = splitting field of some irreducible `Xⁿ - a`) / (`L = K⟮α⟯`, `αⁿ ∈ K`) |
| `autEquivRootsOfUnity` | `:390` | `Gal(L/K) ≃* rootsOfUnity n K` |
| `autEquivZmod` | `:423` | `Gal(L/K) ≃* Multiplicative (ZMod n)` |
| `autAdjoinRootXPowSubCEquiv` | `:249` | `K[ⁿ√a] ≃ₐ[K] L` |
| `X_pow_sub_C_irreducible_iff_of_odd` | `:140` | `Odd n → Irreducible (Xⁿ - a) ↔ ∀ d ∣ n, d ≠ 1 → ∀ b, bᵈ ≠ a` |
| `rootsOfUnity`, `IsPrimitiveRoot`, `rootsOfUnityEquivOfPrimitiveRoots` | `RingTheory/RootsOfUnity/*` | the root-of-unity API |

**Absent.** `KummerTheory`, `IsKummerExtension`, `KummerDedekind` (as a bare constant), `H1` — all
`Unknown identifier` (r1 L136–L138). Specifically:

- No `KummerTheory` file/name; the phrase appears only in docstrings
  (`DedekindDomain/SelmerGroup.lean:49–56`, "will be provided when possible").
- Kummer-theoretic *content* that does exist does so as **Selmer-group bookkeeping**, not as a
  pairing: `IsDedekindDomain.selmerGroup : Subgroup (Kˣ ⧸ n-th powers)` (`SelmerGroup.lean:163`),
  `valuationOfNeZero`, `valuationOfNeZeroMod`. It is stated for fraction fields of Dedekind
  domains — nothing local-field-specific.
- No Galois cohomology of local fields. The only `H¹` in Mathlib is nonabelian sheaf cohomology in
  a topos (`Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean`: `ZeroCochain`,
  `OneCocycle`, `OneCohomologous`), which is a different subject and does not instantiate at
  `Gal(ℚ̄_p/ℚ_p)`.
- No `ℚ_[p]`-specific Kummer statement: no card/structure theorem for `ℚ_p^×/(ℚ_p^×)^n`, no
  `p`-power-root statement, no Kummer extension of a local field.

*What "missing for a local field" precisely means:* the general theorems in `KummerExtension.lean`
are stated over an arbitrary field `K` with `(primitiveRoots n K).Nonempty`, so they **instantiate**
at `K = ℚ_[p]` for `n ∣ p-1` with no new mathematics — only the hypothesis discharge
`Nonempty (primitiveRoots n ℚ_[p])` (Hensel again) and bookkeeping. What does not instantiate is any
statement about the *group* `ℚ_p^×/(ℚ_p^×)^n`, which is what a Kummer *pairing* would need.

### 2.5 Item 5 — ramification and filtration

**Exists, and includes the ramification normalization.** Note two naming traps, both of which cost
one round of `#check` here and would cost more later:

- **`Ideal.ramificationIdx` and `Ideal.ramificationIdx'` are two different definitions in two
  different files.** The *current* one is `Ideal.ramificationIdx`
  (`RingTheory/RamificationInertia/Ramification.lean:52`, length of `Sq/pSq` as an `Sq`-module,
  `0` on non-primes, "This will eventually replace the existing definition"); the *legacy* one is
  `Ideal.ramificationIdx'` (`NumberTheory/RamificationInertia/Ramification.lean:71`,
  `sSup {n | map f p ≤ P^n}`). Their argument orders differ:
  `Ideal.ramificationIdx : Ideal S → (R) → [Algebra R S] → ℕ` vs
  `Ideal.ramificationIdx' : [Algebra R S] → Ideal R → Ideal S → ℕ` (r1 L148–L149). The bridge
  theorem is `Ideal.ramificationIdx'_eq_ramificationIdx` (`RingTheory/…/Ramification.lean:161`).
  **Quoting the wrong one silently changes the statement.** `Mathlib/NumberTheory/RamificationInertia/*`
  (the `'`-suffixed world) is where the *valuation* interface lives; `Mathlib/RingTheory/RamificationInertia/*`
  is the newer abstract world.
- `Ideal.inertiaDeg` exists (`RingTheory/RamificationInertia/Inertia.lean:44`). The legacy
  `Ideal.inertiaDeg'` is declared at `NumberTheory/RamificationInertia/Inertia.lean:69` but carries
  `@[deprecated "Use Ideal.inertiaDeg instead."]`, and a deprecated declaration is no longer
  resolvable — hence `#check @Ideal.inertiaDeg'` reports `Unknown constant` (r1 L152). This is the
  general mechanism behind several "unknown" results: **a `#check` failure cannot distinguish
  "never existed" from "removed by deprecation"**, so §5.3's caveat is not academic.

| Identifier | File:line | Statement |
|---|---|---|
| `Valuation`, `ValuationRing`, `ValuationSubring` | r1 L144–L146 | `Valuation R Γ₀`; `ValuationRing A : Prop`; `ValuationSubring K` |
| `IsDiscreteValuationRing` (class) | `RingTheory/DiscreteValuationRing/Basic.lean:58` | `Prop`; instances: `ℤ_[p]` (`PadicIntegers.lean:525`), `v.adicCompletionIntegers K` (`NumberField/Completion/FinitePlace.lean:78`) |
| `IsDiscreteValuationRing.addVal` | `:405` | `R → AddValuation R ℕ∞` (the additive valuation on a DVR) |
| `addVal_le_iff_dvd`, `addVal_mul`, `addVal_add`, `addVal_uniformizer` | `:455, 432, 469, 428` | the full additive-valuation API |
| `idealOrderIsoENat` | `:513` | `Ideal R ≃o ℕ∞ᵒᵈ` — ideal ↔ exponent dictionary |
| `Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` | `:707` | `(maximalIdeal)ⁿ = {x \| v x ≤ v ϖ ^ n}` |
| `Valuation.IsUniformizer`, `Valuation.IsRankOneDiscrete` | `RingTheory/Valuation/Discrete/Basic.lean:199` etc. | uniformizer machinery, `Γ ≅ ℤ` normalization |
| `Ideal.ramificationIdxIn` | `NumberTheory/RamificationInertia/Galois.lean:59` | Galois-invariant `e`; `ramificationIdx_eq_of_isGaloisGroup` (`:140`) |
| `Algebra.IsUnramifiedAt` | `RingTheory/Unramified/Locus.lean:45` | `FormallyUnramified R (Localization.AtPrime q)` |
| **`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`** | `NumberTheory/RamificationInertia/Valuation.lean:57` | **`v.valuation K x ^ e = w.valuation L (algebraMap K L x)`, `e = ramificationIdx'`** |
| `intValuation_liesOver` | ibid.:44 | same on `A`/`B` |
| `uniformContinuous_algebraMap_liesOver` | ibid.:66 | the inclusion `WithVal (v.valuation K) → WithVal (w.valuation L)` is **uniformly continuous** |
| `HeightOneSpectrum.adicCompletion`, `adicCompletionIntegers` | `RingTheory/DedekindDomain/AdicValuation.lean:602, 806` | completion at a finite place; its integers (`ValuationSubring`) |
| `IsDedekindDomain.HeightOneSpectrum.adicAbv` | `RingTheory/DedekindDomain/AdicValuation.lean:1069` | `AbsoluteValue K ℝ` from a valuation |
| `NumberField.FinitePlace.embedding`, `instNormedFieldValuedAdicCompletion`, `IsRankOneDiscrete` | `NumberField/Completion/FinitePlace.lean:97, 164, 105` | `v.adicCompletion K` is a `NormedField` with a rank-one discrete valuation |

**Answer to the question "does a ramified-extension normalization exist that `Filtration.lean`
could lift to?" — partially, and the precise boundary matters.**

- ✅ The *fraction-field level* normalization exists verbatim: `valuation_liesOver` says
  `v_K(x)^e = v_L(x)` in `ℤᵐ⁰` (multiplicative dressing of `v_L = e·v_K`).
- ✅ The *completion* exists as a `NormedField` with `IsDiscreteValuationRing` integers, for any
  finite place of any number field (`FinitePlace.lean:78, 105, 164`), plus
  `uniformContinuous_algebraMap_liesOver` giving exactly the input needed to pass the identity to
  completions.
- ❌ The *completion-level* identity `v̂_L(algebraMap x) = v̂_K(x)^e` is **not stated in Mathlib**.
  That is the one proposition `Filtration.lean` needs and does not have.
- ❌ There is no `IsRamified` predicate at finite places (`IsRamifiedAt` is `Unknown identifier`,
  r1 L170; the existing `IsRamified` is for *infinite* places,
  `NumberField/InfinitePlace/Ramification.lean:189`). "Ramified" must be spelled as
  `2 ≤ Ideal.ramificationIdx` by hand.
- ❌ `PadicInt.norm_le_pow_iff_mem_span_pow` is `ℤ_[p]`-specific (it goes through `norm_def` and
  `zmodRepr`). For a general DVR the correct analogue is **not** a norm statement — it is
  `addVal`-based (`IsDiscreteValuationRing.addVal_le_iff_dvd` +
  `Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow`). `Filtration.lean`'s four
  norm/ideal lemmas (`Filtration.lean:53–113`) must therefore be **restated** in `addVal` form,
  not copied.

---

## 3. Gap list (each entry is a proposition to prove)

Notation: `p` is a prime, `e := Ideal.ramificationIdx'`, `ℤ_[p]ˣ` etc. as in Mathlib. Items marked
**[prereq]** are needed before the propositions below them compile.

### G1 — bundled valuation decomposition (`ℚ_p^×`)

```lean
-- G1.1  (the decomposition itself)
noncomputable def padicUnitsEquiv (p : ℕ) [Fact p.Prime] :
    ℚ_[p]ˣ ≃* Multiplicative ℤ × ℤ_[p]ˣ
-- component maps:  x ↦ (ofAdd (Padic.valuation x), ⟨x * p^(-v x), _⟩)
-- ingredients:     Padic.valuation_mul, valuation_inv, PadicInt.mkUnits, unitCoeff_coe
```

```lean
-- G1.2  (the compatibility that makes G1.1 useful downstream)
theorem padicUnitsEquiv_apply_val (x : ℚ_[p]ˣ) :
    ((padicUnitsEquiv x).1 : Multiplicative ℤ).toAdd = Padic.valuation (x : ℚ_[p])
theorem padicUnitsEquiv_unit_norm (x : ℚ_[p]ˣ) : ‖(((padicUnitsEquiv x).2 : ℤ_[p]ˣ) : ℤ_[p])‖ = 1
```

There is **no** corresponding `ℤ_[p] ≃* …` gap: a *monoid* iso for `ℤ_[p]` is impossible (`0` breaks
it), and the correct elementwise statement is already exactly `PadicInt.unitCoeff_spec`.

### G2 — Teichmüller splitting of `ℤ_p^×`

```lean
-- G2.1  (surjectivity — already derivable, listed to pin the interface)
theorem PadicInt.units_surj_zmod (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)

-- G2.2  (the section: this is the real work)
theorem exists_teichmuller (p : ℕ) [Fact p.Prime] :
    ∃ τ : (ZMod p)ˣ →* ℤ_[p]ˣ,
      (∀ x, PadicInt.toZMod ((τ x : ℤ_[p])) = (x : ZMod p)) ∧
      (∀ x, τ x ^ (p - 1) = 1)

-- G2.3  (p odd: the product decomposition)
theorem padicInt_units_teichmuller (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nonempty (ℤ_[p]ˣ ≃* ↥(rootsOfUnity (p - 1) ℤ_[p]) × ↥(principalUnits p))
-- principalUnits p : Subgroup ℤ_[p]ˣ  :=  (Units.map toZMod).ker   (= 1 + pℤ_p)

-- G2.4  (p = 2: the exceptional form, a genuinely different statement)
theorem padicInt_units_two :
    Nonempty (ℤ_[2]ˣ ≃* (ZMod 2)ˣ × ↥(principalUnitsOfLevel 2 2))
-- i.e. ℤ_2^× ≅ {±1} × (1 + 4ℤ_2);  note G2.3 is FALSE at p = 2
```

Supporting material for G2.2 that already exists: `hensels_lemma` (unique root in a ball, needs
`import Mathlib.NumberTheory.Padics.Hensel`), `IsCyclic (ZMod p)ˣ`, `IsCyclic.exists_generator`,
`PadicInt.norm_add_eq_max_of_ne` (the "equal norms ⇒ can't cancel" sensitivity the multiplicativity
argument needs). The work is: lift a generator `ζ₀` of `(ZMod p)ˣ` to `ζ : ℤ_[p]` with
`ζ^(p-1) = 1` by Hensel, then show `x ↦ ζ^(log_ζ₀(toZMod x))` is a monoid hom — the hom law is the
part that needs care (both sides are roots of `X^(p-1) - 1` in the same ball, so Hensel uniqueness
finishes).

### G3 — `p`-adic log/exp

```lean
-- G3.0 [prereq]  the one blocked type class
instance (p : ℕ) [Fact p.Prime] : NonarchimedeanRing ℚ_[p]     -- r2 L36 currently fails
instance (p : ℕ) [Fact p.Prime] : NonarchimedeanRing ℤ_[p]     -- r2 L37 currently fails
-- proof route: IsUltrametricDist gives closed balls; closed balls are open additive subgroups;
-- package as NonarchimedeanRing using IsTopologicalRing + is_nonarchimedean
```

```lean
-- G3.1  definition + convergence
noncomputable def padicLog : ℚ_[p] → ℚ_[p]
theorem padicLog_hasSum {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1 : ℚ_[p]) ^ (n + 1) * x ^ (n + 1) / (n + 1)) (padicLog (1 + x))

-- G3.2  multiplicativity  (needs G3.0 for HasSum.mul_of_nonarchimedean)
theorem padicLog_mul {x y : ℚ_[p]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLog ((1 + x) * (1 + y)) = padicLog (1 + x) + padicLog (1 + y)

-- G3.3  injectivity on the principal units (this is what an IUT log-image identity would use)
theorem padicLog_injOn : Set.InjOn padicLog {z : ℚ_[p] | ‖z - 1‖ < 1}

-- G3.4  exp on the convergence locus, and the inverse law
noncomputable def padicExp : ℚ_[p] → ℚ_[p]
theorem padicExp_hasSum {x : ℚ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-(1 : ℤ) / (p - 1))) :
    HasSum (fun n : ℕ => x ^ n / n !) (padicExp x)
theorem padicLog_padicExp {x : ℚ_[p]} (hx : *) : padicLog (padicExp x) = x
```

`G3.1` and `G3.2` are the load-bearing ones; `G3.3` is what a log-image identity actually consumes;
`G3.4` is optional for a first bridge and considerably more work at `p = 2`.

### G4 — local-field Kummer

```lean
-- G4.1  the μ_n hypothesis at ℚ_[p]  (Hensel again; cheap and reusable)
theorem exists_primitiveRoot_padic (p n : ℕ) [Fact p.Prime] (hn : n ∣ p - 1) :
    (primitiveRoots n ℚ_[p]).Nonempty

-- G4.2  instantiate the generic TFAE (no new mathematics, only discharge)
--        KummerExtension.isCyclic_tfae  at  K = ℚ_[p]

-- G4.3  the genuinely missing structure: the group ℚ_p^×/(ℚ_p^×)^n
theorem padic_units_mod_pow_finite (p n : ℕ) [Fact p.Prime] (hn : ¬ (p : ℕ) ∣ n) :
    Finite (ℚ_[p]ˣ ⧸ (powMonoidHom n : ℚ_[p]ˣ →* ℚ_[p]ˣ).range)
-- and its cardinality (n² for (n, p) = 1), which is what a Kummer pairing wants

-- G4.4  (implausible in current Mathlib) Galois-cohomological Kummer pairing
--        H¹(Gal(ℚ̄_p/ℚ_p), μ_n) ≃ ℚ_p^×/(ℚ_p^×)^n
```

### G5 — the ramified-extension lift of `Filtration.lean`

```lean
-- G5.1  completion-level normalization (the missing link; MP present for the input)
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
theorem adicCompletion_valuation_liesOver (x : v.adicCompletion K) :
    (Valued.v x) ^ Ideal.ramificationIdx' w.asIdeal v.asIdeal
      = Valued.v ((algebraMap (v.adicCompletion K) (w.adicCompletion L)) x)
-- from: valuation_liesOver (fraction-field level) + uniformContinuous_algebraMap_liesOver
--       + continuity/density of the completion map

-- G5.2  DVR-form layer lemma (replaces the ℤ_p-specific norm lemma)
theorem mem_maximalIdeal_pow_iff_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔ n ≤ IsDiscreteValuationRing.addVal R x
-- from: addVal_le_iff_dvd + idealOrderIsoENat + maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
--       (all three already exist; this is bookkeeping, not new mathematics)

-- G5.3  a "ramified" predicate at finite places (absent; must be coined)
def RamifiedAt (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) : Prop :=
  2 ≤ q.ramificationIdx R
```

`G5.1` is the *only* item in G5 that is genuinely new mathematics-adjacent work; `G5.2` and `G5.3`
are interface work.

---

## 4. Cost verdict

Estimates assume a Lean-fluent implementer working against this pinned Mathlib, no upstream
dependencies, and include statement iteration (the usual 2–3× over the informal proof). They are
estimates, not measurements — nothing below was attempted.

| # | Item | Verdict | Cost | Why (grounded in §2) |
|---|------|---------|------|----------------------|
| 1 | `ℚ_p^× ≅ ℤ × ℤ_[p]^×` | partial | **hours (≈ 0.5–1 day)** | Every ingredient is a named lemma: `PadicInt.unitCoeff_spec` gives the elementwise factorization, `Padic.valuation_mul`/`valuation_inv` give the hom laws for units (the `≠ 0` side conditions are free on `ˣ`), `PadicInt.mkUnits` builds the unit. Only the `MulEquiv` is missing; the `≃+*`-free nature (it is a monoid iso, not a ring iso) means no algebraic obstructions. |
| 2a | residue-field / `ZMod` half of `ℤ_p^×` | **exists** | **0** | `PadicInt.residueField`, `toZMod`, `ker_toZMod`, `toZModPow`, `norm_le_pow_iff_mem_span_pow` are all in place with exactly the needed forms (`Filtration.lean` already uses two of them). |
| 2b | `(1+pℤ_p)` quotient | partial | **hours** | `IsLocalRing.surjective_units_map_of_local_ringHom` + `ZMod.ringHom_surjective` gives surjectivity `ℤ_[p]ˣ ↠ (ZMod p)ˣ` in ~10 lines (the `IsLocalHom PadicInt.toZMod` side condition follows from `PadicInt.ker_toZMod`); `ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits` gives the quotient iso for free *if* one first builds `ValuationSubring ℚ_[p]` for `ℤ_[p]` (absent, `Padics/Complex.lean:251` shows the pattern for `ℂ_[p]`). |
| 2c | Teichmüller splitting / `μ_{p-1}(ℤ_p)` | partial | **days (≈ 2–5 days)** | Hensel is available in the exact form needed (`hensels_lemma` with uniqueness), `IsCyclic (ZMod p)ˣ` supplies a generator, `PadicInt.norm_add_eq_max_of_ne` supplies the ball sensitivity. The cost is the *hom law* (`τ(xy) = τ(x)τ(y)`), not existence; plus a separate `p = 2` statement (G2.4), which is a different theorem, not a case split. Not weeks, because no new analysis is required. |
| 3 | `p`-adic `log` | **absent** | **weeks (≈ 3–6)** | Convergence inputs are all present (`dividedPowers`, `padicValNat_factorial_lt_of_ne_zero`, `padicValNat_le_nat_log`, `Padic.nonarchimedean`, `summable_iff_tendsto_cofinite_zero`, `CompleteSpace`), so G3.1 is perhaps a week. G3.2 (multiplicativity) is the expensive step: the double-series rearrangement is not idiomatic Mathlib material, and the one generic lemma for it (`HasSum.mul_of_nonarchimedean`) is blocked by the missing `NonarchimedeanRing ℚ_[p]`. G3.3 (injectivity) is another chunk (needs the `log`-of-`1+pⁿ`-vanishing analysis). `NormedSpace.exp` offers nothing (no `NormedAlgebra ℚ ℚ_[p]`, and correctly so). |
| 3' | `p`-adic `exp` | **absent** | **+2–4 weeks** | Beyond G3.1–G3.3: the truncated-radius analysis (`‖x‖ < p^{-1/(p-1)}`), the `p = 2` adjustment (`4ℤ_2`), and `log ∘ exp = id`. Each is a separate convergence argument, none of them helped by existing Mathlib API. |
| 3'' | Lubin–Tate formal group | **absent** | **implausible (> months)** | Zero declarations; would require formal-group theory over `ℤ_p`, which does not exist in Mathlib in any form. Only worth attempting if a specific bridge target demands it. |
| 4 | Kummer | partial | **days for the instantiation, implausible for the pairing** | `isCyclic_tfae`/`autEquivZmod`/`X_pow_sub_C_irreducible_iff_of_odd` are general in `K`, so G4.1+G4.2 ≈ 2–4 days (mostly the Hensel-based `μ_n ⊆ ℚ_[p]`). G4.3 (`ℚ_p^×/(ℚ_p^×)^n`, its finiteness and order) is a self-contained weeks-scale project. G4.4 (Galois cohomology of local fields) is **implausible** — Mathlib has no Galois cohomology, only topos-theoretic `H¹`. |
| 5 | ramification / filtration | **exists** | **days (≈ 2–4) for the `Filtration.lean` lift** | The hard inputs exist: `valuation_liesOver` (the normalization), `uniformContinuous_algebraMap_liesOver` (the passage to completions), `IsDiscreteValuationRing.addVal` + `idealOrderIsoENat` + `maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` (the layer dictionary). Missing: G5.1 (completion-level identity, one continuity/density argument), G5.2 (bookkeeping), G5.3 (naming). **Caveat:** `PadicInt.norm_le_pow_iff_mem_span_pow` cannot be reused; the lift must be restated in `addVal` form, which is a rewrite of roughly the four lemmas at `Filtration.lean:53–113`. |

### The single largest missing piece

**The `p`-adic logarithm (item 3), together with its enabling type class
`NonarchimedeanRing ℚ_[p]`.**

It is the only item where the *mathematics* (not just the interface) is missing: convergence inputs
are complete, but there is no series API over `ℚ_[p]`, `NormedSpace.exp` is unusable by design
(`NormedAlgebra ℚ ℚ_[p]` is impossible), and the one generic product-of-`HasSum`s lemma is gated
behind a class that fails to synthesize. Everything else is interface work measured in days.

The **cheapest genuinely useful next step** is `instance : NonarchimedeanRing ℚ_[p]` (G3.0):
it is tens of lines from `IsUltrametricDist` (whose `NonarchimedeanAddGroup` half already fires,
r2 L35), it unblocks `HasSum.mul_of_nonarchimedean`, and that single lemma is the gate for the
multiplicativity proof of both `padicLog` (G3.2) and the Teichmüller hom law (G2.2) — i.e. it is
on the critical path of the two most expensive items at once.

---

## 5. What this does NOT establish

1. **Nothing about IUT/Θ-links.** No probe touches Hodge theaters, Θ-links, log-volumes, the
   `U`-invariant, or the arithmetic deformation. This document is an inventory of *p-adic
   infrastructure only*. Whether an actual IUT bridge "needs" items 1–5 in this form is a
   mathematical question this round did not test; it assumed the task's list.
2. **No proof was attempted.** Every verdict is `#check`/`#synth`-grade. In particular,
   "exists" means *the statement is present at that name*, not that the statement is the one a
   bridge needs, and certainly not that its proof is axiom-clean. We did not audit for `sorry`,
   `native_decide`, or extra axioms anywhere in Mathlib; we rely on Mathlib's own policy.
3. **`absent` means "not found", not "not present".** Grep is textual and `#check` is
   name-directed, and a `#check` failure cannot even distinguish *absent* from *deprecated away*
   (direct evidence: `Ideal.inertiaDeg'` is declared but `@[deprecated]`, so it reports
   `Unknown constant`, §2.5). A lemma with a different name and the same content would be missed.
   This was mitigated only where the check was *semantic* rather than name-based — `#synth` for type
   classes (`Valued ℚ_[p]`, `NonarchimedeanRing ℚ_[p]`, `NormedAlgebra ℚ ℚ_[p]`,
   `HasSummableGeomSeries ℚ_[p]`, `IsDiscreteValuationRing ℤ_[p]`) and directory-wide greps for
   `rootsOfUnity`/`IsPrimitiveRoot`/`X_pow_sub` inside `NumberTheory/Padics/**`. Those three
   absences (Teichmüller-in-`ℤ_p`, `p`-adic log, series product in `ℚ_[p]`) are the ones we are most
   confident in; the rest of the "absent" list should be read as "no such name".
4. **One "absent" is only an instance gap, and is flagged as such.** `Valued ℚ_[p] NNReal` fails
   `#synth` but is one line of `NormedField.toValued`. Conversely, `#synth` failure never proves
   *impossibility* — it proves only that no instance is registered for the goal as stated.
   `NormedAlgebra ℚ ℚ_[p]` is the one case where we claim impossibility, and the reason is
   mathematical (the archimedean norm on `ℚ` cannot be multiplicative for the `p`-adic norm), not
   merely a missing-instance observation.
5. **No `lake build`, no writes to the main checkout, no olean written.** The probes were run with
   `lake env lean --json` and no `-o`; the main checkout `D:\Inter-universal Teichmüller Theory`
   was read only. `EXIT=1` on every probe round is the expected consequence of the
   deliberately-absent names, not a tooling failure.
6. **The cost verdicts are estimates.** No line of the gap list was implemented. The `hours` vs
   `weeks` boundary is a judgement about how much *existing generic API* the proof can lean on; it
   is not a measurement, and it is the part of this report most likely to be wrong.
7. **Pinned-revision scope.** All findings are for Mathlib `85e3a25e…` on Lean `v4.34.0-rc2`. Item 5
   in particular is visibly mid-refactor (`ramificationIdx` replacing `ramificationIdx'`), so that
   part may date quickly. `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` and
   `RingTheory/RamificationInertia/*` carry 2026 copyright dates — this is moving code.
8. **`Filtration.lean`'s own claims were not re-audited.** We read it to fix the lift target; we did
   not verify its theorems.

---

## Appendix — probe inventory

| File | Purpose |
|---|---|
| `probe-padic-inventory-round1.lean` (+ `probe-round1-digest.txt`) | 89 `#check`s across items 1–5, including the deliberately-absent names |
| `probe-padic-inventory-round2.lean` (+ `probe-round2-digest.txt`) | namespaced re-probes (`Ideal.IsUnramifiedAt` → `Algebra.IsUnramifiedAt`, `Ideal.ramificationIdx'_eq_ramificationIdx`, `IsDedekindDomain.HeightOneSpectrum.adicAbv`), imports for `WittVector.teichmuller`/`Perfection.teichmuller`, and the `#synth` battery |
| `probe-padic-inventory-round3.lean` (+ `probe-round3-digest.txt`) | constructibility checks: `NormedField.toValued : [NormedField K] → [IsUltrametricDist K] → Valued K NNReal`, `IsUltrametricDist.nonarchimedeanAddGroup`, `IsCyclic.exists_generator` |
| `probe-padic-inventory-round4.lean` (+ `probe-round4-digest.txt`) | `hensels_lemma`'s root namespace (it is `_root_.hensels_lemma`, requiring `import Mathlib.NumberTheory.Padics.Hensel`) and the full uniqueness statement |

Digest format: `L<line> <severity> <message>`, with `line` being the line in the corresponding
`.lean` file, so each entry maps to exactly one probe. `information` = the constant resolved and
its type is printed; `error` = unknown constant, or a `#synth` failure.
