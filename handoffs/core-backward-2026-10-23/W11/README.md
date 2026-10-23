# W11 — `EtaComparison.lean`: the (9-1) shape, in the smallest model where it has content

Date: 2026-10-23. Status: **toy province, machine-checked, delivered**. Not a fact-tree entry, not a
registry entry, not an audit of any IUT object. The core GAP of `research/core-backward-2026-10-23/`
stays **OPEN**.

## Scope

`research/core-backward-2026-10-23/lana-report-assessment.md` §5b records that (9-1) is already a named
equivalence in the audited upstream interface — `Iut/Wall/EtaAlg.lean:151`
`etaAnab_eq_etaQ_iff` : `A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs`,
whose docstring says "an equation between two maps of pointed lines *is* an equation of real numbers" —
and §5c asks W7's "equality on the orbit" toy to be aligned with it. This file is that toy: elementary
linear algebra over `ℝ`, no interface of the real construction.

Two pointed lines `Rval := ℝ` and `Rss := ℝ` (both one-dimensional), maps `Rval →ₗ[ℝ] Rss`, the pointing
carried by a chosen non-zero real `p` (the pilot). Two families: `etaAnab c s = scalarMap (c s)` indexed by
a choice `S`, and `etaQ q = scalarMap q` for a single scalar. `scalarMap a` is multiplication by `a`,
which is what `ValBPS.eta` is once the pilot coordinate is put on the source.

## Deliverable

| item | value |
|---|---|
| file | `candidates/core-transport/EtaComparison.lean` (**did not exist** before this round; created) |
| namespace | `EtaComparison`; import `CoreLog.QpThree` (only) |
| sha256 | `330431eddd7e3e722723338faba0b59c10f649bfd73279c62ccaa9285425cfce` |
| bytes / chars / lines | 28381 / 27517 / 483 (LF-only, no CR, no BOM, final newline) |
| declarations | 43 (9 `abbrev`/`def`, 34 `theorem`), 43 `#print axioms` lines |
| build | exit **0**, stdout 3968 B (the 43 footprint lines and nothing else), stderr **0 B**, 0 warnings |

No existing file was modified: `tools/`, the fact tree, the registry, the other candidates and the two
toys are untouched (`git status` shows `EtaComparison.lean` as the single addition inside the package).

## Commands

From `D:\Inter-universal Teichmüller Theory\candidates\core-transport`:

```
lake env lean -DwarningAsError=true EtaComparison.lean
```

Raw logs in this directory: `build.stdout.log` (3968 B), `build.stderr.log` (**0 B**), `build.exit.txt`
(exit `0`), `axioms.txt` (the footprint output, verbatim), `checks.txt` (hashes, counts, scans). The file is
not a Lake target, so no `.olean` is produced.

## The chain that is actually proved

1. **The reduction lemma** (heart of `etaAnab_eq_etaQ_iff`), line 155:

   ```lean
   theorem map_eq_iff_pilot (f g : Rval →ₗ[ℝ] Rss) (p : ℝ) (hp : p ≠ 0) :
       f = g ↔ f p = g p
   ```

   Forward is `LinearMap.congr_fun`; backward is `LinearMap.ext` on the basis vector `p`, through
   `x = (x / p) • p`. Companion: `map_eq_scalarMap (f) : f = scalarMap (f 1)` — a map of pointed lines
   has no freedom beyond the image of one non-zero point (upstream `ValBPS.eta_unique`).

2. **(9-1) for one `S` is an equation of numbers**, line 244:

   ```lean
   theorem eta_equality_iff_scalar {S : Type*} (c : S → ℝ) (q : ℝ) (S₀ : S) :
       etaAnab c S₀ = etaQ q ↔ c S₀ = q
   ```

   proved as the `p = 1` case of `eta_equality_iff_scalar_via_pilot` (line 234), which proves
   `etaAnab c S₀ = etaQ q ↔ c S₀ = q` at an arbitrary pilot by going through the intermediate
   `etaAnab c S₀ p = etaQ q p` and cancelling `p ≠ 0` (`pilot_eq_iff_scalar`). The quantifier form is
   `exists_eta_eq_iff_exists_scalar : (∃ S₀, etaAnab c S₀ = etaQ q) ↔ ∃ S₀, c S₀ = q`.
   Candidate-*isomorphism* status: `etaAnab_bijective`, `etaQ_bijective` (bijective iff the scalar is
   non-zero).

3. **The orbit form.** The units `ℝˣ` act on the scalars by `u • x = u * x` (`unit_smul_eq_mul`); a
   subgroup `H ≤ ℝˣ` is the indeterminacy; the family is indexed **by the indeterminacy itself**,
   `orbitFamily H c₀ s = s • c₀`, so the choice `S` of (9-1) *is* an element of the group. Then

   ```lean
   theorem eta_eq_iff_inOrbit (H : Subgroup ℝˣ) (c₀ q : ℝ) :
       (∃ s : H, etaAnab (orbitFamily H c₀) s = etaQ q) ↔ InOrbit H c₀ q
   ```

   with `InOrbit H c q := ∃ u : ℝˣ, u ∈ H ∧ q = (u : ℝ) * c`, and the literal form the task asks for,
   line 313:

   ```lean
   theorem in_orbit_iff_exists_iso_in_family (H : Subgroup ℝˣ) (c₀ q : ℝ) :
       (∃ S₀ : H, etaAnab (orbitFamily H c₀) S₀ = etaQ q) ↔
         ∃ S₀ : H, InOrbit H (orbitFamily H c₀ S₀) q
   ```

   The constructive direction is `exists_S_of_inOrbit`; `nine_one_at_four` is a case where the toy's
   (9-1) holds with an explicit choice; `top_inOrbit_iff` shows that with the whole unit group the orbit of
   a non-zero scalar is every non-zero scalar, so the only unreachable target is `0`.

## Degeneracy, both directions, with the numbers

* **Zero pilot kills the reduction.** `idMap = scalarMap 1`, `doubleMap = scalarMap 2`;
  `idMap_ne_doubleMap` (values `1` vs `2` at `1`) while `idMap 0 = 0 = doubleMap 0`. Hence
  `agreement_at_zero_not_determining : ∃ f g, f ≠ g ∧ f 0 = g 0`,
  `zero_pilot_not_determining`, and `map_eq_iff_pilot_fails_at_zero`. So `hp : p ≠ 0` is not removable.
* **Scalar outside the orbit, no `S` works.** With `H = ⊥` the family is the single map `scalarMap 1`
  (`orbitFamily_bot`); the target is `q = 2`, and `not_inOrbit_bot : ¬ InOrbit ⊥ 1 2` records the
  non-membership on its own. `bottom_pointwise` exhibits the failure at the pilot (every member sends `1`
  to `1`, `etaQ 2` sends it to `2`) and `no_S_below_bottom : ¬ ∃ s : ⊥, etaAnab (orbitFamily ⊥ 1) s = etaQ 2`
  proves no choice gives equality — while all maps involved are isomorphisms, so this is a genuine orbit
  failure, not a collapse. A second, sharper failure: `no_S_top_zero` with `H = ⊤`, `c₀ = 1`, `q = 0`
  (the target is the zero map, so it is not an isomorphism at all).

## Dependency footprint

All 43 declarations, the `def`s and `abbrev`s included, print the same verbatim form:

```
'EtaComparison.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Union: `{propext, Classical.choice, Quot.sound}` — inside the allowed set; `sorryAx` 0 times in the log.
Forbidden substrings in the file (docstrings included): `sorry` 0, `admit` 0, `opaque` 0,
`native_decide` 0; the 43 occurrences of `axiom` are exactly the 43 mandated `#print axioms` lines.

## Non-claims

1. **This does not prove (9-1).** It proves a statement about `ℝ →ₗ[ℝ] ℝ`; (9-1) is a statement about
   `A.etaAnab ι S` and `etaQ D`, linear maps out of a value-group BPS built from `out`, `BPS`, `Ind3`,
   `logVol`, `qPilot`.
2. **No `out`, no `BPS`, no `Ind3`, no `logVol`, no Θ-link, no Hodge theater, no volume container, no
   log-shell, no `Ism`, no `Ind1`/`Ind2`** occurs in the code. `S` is an arbitrary type, `H` an arbitrary
   subgroup of `ℝˣ`, `c` an arbitrary `S → ℝ` (not a log-volume), `q` an arbitrary real (not `−|log q|`).
3. The toy's (9-1) is a theorem *of the toy*: that "some choice gives equality" is equivalent to an orbit
   condition is a fact about multiplication on `ℝ`, and carries no information about the real
   constructions. Upstream's `Wall` hypothesis is an open proposition about those constructions; nothing
   here implies or refutes it.
4. **The indeterminacy is not modelled as an action on the index set**: `Ind1`/`Ind2` act on the
   (Ind3)-choices upstream, but here the family is only indexed by the subgroup — the file says which
   scalars the choices produce, not how the choices are permuted.
5. Not evidence for or against any IUT claim. Core GAP OPEN; `fact_tree_admitted` false.
