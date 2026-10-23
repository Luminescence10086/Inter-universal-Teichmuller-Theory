# M4 — missing.md

Scope: static search only, in `reviews/core-round/external/iut` (HEAD `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`, verified — no `INPUT_DRIFT`) and the local Mathlib checkout. No Lean, no lake, no clone, no build. 8 hits tabulated in `reuse.csv`; nothing outside them is claimed.

## Need 1 — a collection of local objects + global objects + localization isomorphisms

**Partially found, at the level of data shape only, and the isomorphisms are gone.**

- `Iut.ThetaLink.RlfMuStrip` (M4-05) is this repository's own encoding of IUT II Definition 4.9(viii), whose docstring quotes the original as exactly "a collection `(C^⊛, Prime(C^⊛) ≅ V, F^{⊛±⋊×μ}, {ρ_v})`: a global realified Frobenioid, an `F^{⊛±⋊×μ}`-prime-strip …, and the isomorphisms `ρ_v` identifying the realified local value groups with the local data of `C^⊛`". That is need 1 almost verbatim.
- **How far:** definition only, and a *reduced* definition. The same docstring records the reduction: "the splitting monoids `O^▷` and the Frobenioid `C^⊛` itself are recorded only through their realified value groups and the local pilots". In Lean the object is two fields, `unit : FMuStrip D` and `val : ValBPS (Pl D) D.bpsDegrees.bad` (lines 159–163). The `ρ_v` therefore **do not occur as fields, maps, or morphisms**; their *images* `localPilot v` do. So the "localization isomorphisms" leg of need 1 is present in the prose, absent in the type.
- `Iut.Wall.ValBPS` (M4-04) is the value-group half on its own: one global real line `C` with `localPilot : V → C`, `localPilot_ne_zero`, `pilot_ne_zero`, `finrank_eq_one`. This is "local pieces inside one global object", not a span of local objects.
- There is **no** structure anywhere in the searched space whose fields are (i) a genuinely local object at each `v` (a local Frobenioid `C_v` with its own `O^▷`, divisor monoid, etc.), (ii) a global object, (iii) localization morphisms between them as data. Not found. Also not found: any descent/gluing statement (that the local data determine the global object, or conversely), which is what K2/H2 actually needs.

## Need 2 — objects with a group action and equivariant morphisms

**Found, for one specific category, with real proofs.**

- `Iut.Frobenioid.OrbitObj` / `Iut.Frobenioid.OrbitHom` (M4-01). Objects are transitive `G`-sets `G ⧸ H` with `H` **open**; a morphism is a map with `map_smul : ∀ g x, toFun (g • x) = g • toFun x`.
- **How far:** full for that category. Equivariance is a *field* of the morphism structure (so it is enforced by the type, not proved), while the nontrivial statements are genuine theorems with real proofs: `OrbitHom.surjective` (87 — equivariant maps of transitive `G`-sets are surjective), `OrbitHom.injective_of_mono` (163), `OrbitHom.bijective_of_isFSM` (178), `OrbitObj.isConnected` (116), `OrbitObj.totallyEpimorphic` (121). Premise `[IsTopologicalGroup G]` is needed only for 163/178.
- **Not found:** a group action *on* local/global objects of need 1 with equivariant morphisms between them — i.e. equivariance of Frobenioid morphisms under `Gal`/`O^▷` acting on prime-strips. The Galois material that does exist (`Iut/Frobenioid/GaloisModel.lean`, `GaloisBase.lean`) acts on the *base category* only, and is a separate construction, not a general equivariant-morphism theory for IUT objects. `OrbitObj` is the tempered base category `B^temp(Π)⁰`; it carries no divisors and no pilots.

## Need 3 — concrete data for a structural poly-morphism / orbit, and the allowed morphisms

**Partially found. The orbit category exists; an explicit "poly-morphism" type does not.**

- Orbit side: `OrbitObj`/`OrbitHom` (M4-01) is a concrete orbit category, with `Iso`-class structure and the `Category` instance proved.
- Morphism side: `RlfMuStrip.Iso` (M4-05, 171–175) and `ValBPS.Iso` (M4-04, 231–235) give the allowed morphisms for the BPS/prime-strip data: a pair (unit iso, value iso), resp. a linear iso carrying `localPilot v` to `localPilot v`.
- **How far:** the repo models the *indeterminacy* of a poly-isomorphism by **making the value part a subsingleton**: `ValBPS.valIso_subsingleton` (296) and `RlfMuStrip.Iso.val_eq` (208) prove any two value isomorphisms agree, and `RlfMuStrip.isoEquivUnit` (214) proves the whole Hom is equivalent to the unit part. So "poly-morphism" is represented as "the unit part is the only freedom", which is a *consequence derived after the fact*, not a structure named `PolyMorphism` with an action on readings.
- **Not found:** a type whose elements are structural poly-morphisms (indeterminacy classes) with a proved action on pilot values; and no statement that such a class is closed under composition except through the ordinary `Iso.refl/symm/trans` of the two component structures. Elsewhere indeterminacy is modelled as explicit *sets of automorphisms* (`LocalTheory.archIndAut`, `LocalTheory.indAut`), not as a poly-morphism object.

## Need 4 — a construction theorem that pullback / base change preserves those structures

**The key negative result of this task: in the general case this is an ASSUMED FIELD, not a theorem.**

- `Iut.Frobenioid.IsFrobenioid` (M4-02) is a `Prop`-valued structure with one field per clause of [FrdI] Definition 1.3. Clause (i)(c) is
  `pullback_surj : ∀ (A : C) (X : D) (f : X ⟶ base P A), ∃ (B : C) (φ : B ⟶ A) (e : base P B ≅ X), IsPullback P φ ∧ e.hom ≫ f = Base P φ` (250–252).
  That is *exactly* "pullback exists and preserves the structure", and it is a **hypothesis you must supply**. `base_surj`, `preStep_span`, `frobenius`, `coslice_surj`, `slice_surj` are in the same position. `IsPullback` (135–137) is only the universal-property predicate. `IsFrobenioid` is Prop-valued and constructs nothing.
- Existence *is* proved, but only for specific categories: `Iut.Frobenioid.Model.isFrobenioid` (M4-03, 302–347) discharges every clause for the model Frobenioid, and the pullback is literally built — `Model.pullback_surj` (121–126) produces the object `⟨Y, Φ.pb f X.α⟩` with morphism `mk1 f 0 (Φ.pos _).zero_mem 0 (by simp)`. A second, non-model discharge is `Iut.Frobenioid.Angular.isFrobenioid` (`Iut/Frobenioid/Angular/Frobenioid.lean:106`), where pullback morphisms are exactly the isomorphisms (`isPullback_iff`) — a degenerate case, useful mainly as a warning that "the clause holds" can be vacuous.
- Base-change degree: `Iut4Sec1.arithmeticDivisorDegree_pullback` / `..._normalizedArithmeticDivisorDegree_pullback` (M4-08) do give a genuine base-change computation for arithmetic divisors.
- **Not found:** any theorem that pullback/base change along the *actual IUT operations* (log-link, Θ-link, cQ3/cQ4, the procession) preserves the structures of needs 1–3; and nothing about whether the required associations survive descent to a formal/stack-theoretic quotient (H2) — the searched space contains no quotient-descent statement for these objects at all. The model construction also presupposes `Φ : DivMonoid D`, `B : GrpOn D`, `divB : DivHom B Φ.toGrpOn` as supplied data; it does not build them from a curve.

## Need 5 — naturality of determinant / tensor power and the induced degree transformation

**Split: the determinant half exists only for a real endomorphism at ∞; the degree half exists but is either a certificate projection or a Frobenioid/divisor degree.**

- Determinant: `Iut.LogLink.abs_det_archIndMap` (M4-06, 327) proves `|LinearMap.det (archIndMap c σ ε)| = 1` for `archIndMap c σ ε = PiTensorProduct.map (fun j => archFactorMap (σ j) (ε j))` — i.e. the determinant of a **tensor product of factor maps** `⊗_j (ε_j·σ_j)`, the archimedean indeterminacies. Proved (via the Haar scaling law and log-shell invariance), not assumed. Group functoriality: `archIndMap_mul` (372), `archIndMap_one` (381). **Boundary:** this `LinearMap.det` is measured against a chosen Haar measure on a real vector space; it is not a determinant of a line bundle or of a Frobenioid object, yields no degree/log-volume formula for tensor powers of a line, and says nothing at the non-archimedean places or about prime-strips.
- Degree, Frobenioid side: `GlobalRealified.degree_frobenius` (M4-07, 328) gives `Y.degree = φ.deg * X.degree` for a morphism of Frobenius type. **Trap:** its proof is `h.1.2` — a *field* of the supplied `IsFrobeniusType` certificate (`Div φ = 0`) — substituted into `degree_hom` (305). It projects a field out of a certificate; it does not construct a degree map. `degree_hom` itself, `(φ.deg : ℝ) * X.degree + degArith K φ.div = Y.degree`, is a real identity. Because `degFr = n` precisely for the degree-`n` Frobenius/tensor-power object (`Model.frobenius`, `ModelFrobenioid.lean:130`, object `⟨X.base, n • X.α⟩`), this is the nearest existing "degree transformation under tensor power".
- Degree, base-change side: `Iut4Sec1` `arithmeticDivisorDegree_pullback` (raw degree scales by `[L : K]`) and `normalizedArithmeticDivisorDegree_pullback` (normalized degree invariant) — genuine place-by-place computation. Its own README boundary: the globally normalized quotient of IUT IV Definition 1.9(ii) is deliberately **not** claimed.
- **Not found:** naturality of the determinant (or of a fixed tensor power `Θ^{⊗M}`) of a *line* under a structural poly-morphism; any `tensorPower` construction on IUT objects; and the induced transformation of the *normalized log-volume* degree that cQ3 actually uses. No declaration in the searched space states "det/tensor-power is natural with respect to the allowed morphisms of need 3".

## Where a "theorem" only extracts a field from a supplied certificate

- `Iut.Frobenioid.IsFrobenioid.pullback_surj` / `base_surj` / `frobenius` / `coslice_surj` / `slice_surj` — fields. For an arbitrary `P` these are *assumptions*; only `Model.isFrobenioid` and `Angular.isFrobenioid` discharge them.
- `GlobalRealified.degree_frobenius` — extracts `IsFrobeniusType`'s `Div φ = 0`.
- `ValBPS.Iso.map_pilot` (253) and `RlfMuStrip.Iso.map_pilot` (192) — derived from the field `map_localPilot`, i.e. the conclusion is already in the certificate.
- By contrast, genuinely *proved* content: `OrbitHom.surjective` / `injective_of_mono` / `bijective_of_isFSM`, `OrbitObj.isConnected` / `totallyEpimorphic`, `abs_det_archIndMap`, `degree_hom`, `arithmeticDivisorDegree_pullback`, `normalizedArithmeticDivisorDegree_pullback`, `Model.pullback_surj` (as a construction), `ValBPS.valIso_subsingleton`, `ValBPS.eta_unique`.

## Definition vs existence (per hit)

| hit | type or class only ("allows") | existence proved | how |
|---|---|---|---|
| M4-01 `OrbitObj`/`OrbitHom` | yes, structure + `Category` instance | trivially inhabited (`top := ⟨⊤, isOpen_univ⟩`, 105) | not an existence theorem, and none is needed |
| M4-02 `IsFrobenioid` | yes, `Prop`-valued class | **no** | must be discharged per `P` |
| M4-03 `Model.isFrobenioid` | — | **yes**, for model Frobenioids | construction `⟨Y, Φ.pb f X.α⟩`, `⟨X.base, n • X.α⟩` |
| M4-04 `ValBPS` | yes, structure | **no** for a general `V`; yes via `qVal` | `Iut/Wall/Pilots.lean:106` from `L : LocalDegrees V` with `L.bad` nonempty, `L.deg > 0` |
| M4-05 `RlfMuStrip` | yes, structure | **conditional**, not for arbitrary `D` | `qStrip` (239) / `gauStrip` only from a given `ThetaPmEllNFHT` |
| M4-06 `abs_det_archIndMap` | — | theorem | fully proved |
| M4-07 `degree_frobenius` | — | theorem, but consumes a certificate | field projection |
| M4-08 `...Degree_pullback` | — | theorem | fully proved |

## Generic-lemma warning and Mathlib

Mathlib was consulted for exactly one name check, and is **not** tabulated as a hit: `Mathlib.CategoryTheory.Localization.HasLocalization` exists (in the local checkout, `Mathlib/CategoryTheory/Localization/HasLocalization.lean:54`), but it is *category localization* (formally inverting a class of morphisms). The "localization isomorphisms" of need 1 are `ρ_v` identifying realified local value groups with local data of `C^⊛`; they are not a localization functor and no Mathlib lemma applies. The same caution applies to the generic category-theoretic material the external repo builds on (`CategoryTheory.EpiMono`, `IsConnected`, `TotallyEpimorphic`, `PiTensorProduct.map_comp`): its existence says nothing about IUT — every use in the hits above is a *specific* instantiation that had to be proved in place.

**Revision caveat (affects any future name reuse).** The external repo pins `mathlib` `rev = "v4.32.0"` (`lakefile.toml`), while the local Mathlib checkout is at `85e3a25e006c35636f0e53b0e9296caca2685bc0` with `leanprover/lean4:v4.34.0-rc2`. The two are different revisions, so a Mathlib name quoted from the local checkout may not exist, or may have a different statement, under the external repo's dependency. This does not affect the hits above, all of which are declarations of the external repo itself.

## Not searched / out of scope

Not searched: any other GitHub repository, `local-field/`, `bridge/`, `candidates/core-*` in this workspace (no duplication was found to be likely, and the fixed search space was sufficient), the III PDF/TXT, and any IUT object construction. No Lean was run; "proved" above always means "carries a proof term in the source as read", not "kernel-checked here".
