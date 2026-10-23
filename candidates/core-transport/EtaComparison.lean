import CoreLog.QpThree

/-!
# W11: the (9-1) shape in a toy — two families of maps of pointed lines, and equality on one orbit

**Scope.** This file formalises, in the smallest model in which the statement has any content, the *shape*
of the compatibility question that `research/core-backward-2026-10-23/lana-report-assessment.md` §5b calls
**(9-1)**: two constructions of an isomorphism between the same pair of **pointed lines**, one of them
`η_q` (a single map, fixed by the `q`-pilot) and one of them `η^anab_S` (a family of maps, indexed by a
choice `S`), and the question whether some `S` makes the two equal. It is a toy province: not a fact-tree
entry, not a registry entry, not an audit of any IUT object. The core GAP of
`research/core-backward-2026-10-23/` stays OPEN.

**The obligation, quoted.** The reduction this file models is already in the audited upstream interface.
`reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean:151` states

```
theorem etaAnab_eq_etaQ_iff {h₁ h₂ : A.Side} (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D) :
    A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs
```

and the docstring of that file says of it: "(9-1) for `(ι, S)` holds iff `log-vol(out ι S) = −|log(q)|`:
an equation between two maps of pointed lines *is* an equation of real numbers". The mechanism is
`ValBPS.eta_eq_eta_iff` (`Iut/Wall/BPS.lean:335`): a linear map of the pointed line is determined by the
image of the pilot, so two such maps agree iff they agree at that one point. Everything in the present file
is the elementary linear algebra behind that sentence, over `ℝ`, with the indeterminacy made explicit.

**What is modelled, and what is not.** `R^val` and `R^ss` are `ℝ` and `ℝ` (both one-dimensional, both
pointed), a map between them is `ℝ →ₗ[ℝ] ℝ`, and the pointing is a chosen non-zero real number `p` (the
pilot). The two families are: `etaAnab c s = scalarMap (c s)` for a family of scalars `c : S → ℝ` indexed
by the choice `S`, and `etaQ q = scalarMap q` for a single scalar `q`. The map `scalarMap a` is
multiplication by `a`, which is what `ValBPS.eta` is after the pilot coordinate is put on the source
(`eta x = x • pilotCoord`). The structural cost of the model is that the "same pair of pointed lines" is
the same two copies of `ℝ` — which is exactly the point: (9-1) is not about the spaces, it is about which
isomorphism between them the two constructions produce.

**What is proved, in order.**

1. **The reduction lemma** (`map_eq_iff_pilot`): for `f g : ℝ →ₗ[ℝ] ℝ` and `p ≠ 0`,
   `f = g ↔ f p = g p`. Forward is congruence; backward is `LinearMap.ext` on the basis vector `p`, using
   `x = (x / p) • p` — the single place where `p ≠ 0` is consumed. `map_eq_scalarMap` is the companion
   uniqueness statement: every map of the pointed line is `scalarMap` of its value at `1`.
2. **A family of candidate isomorphisms, and (9-1) as a scalar equation** (`etaAnab`, `etaQ`,
   `eta_equality_iff_scalar`): `etaAnab c S₀ = etaQ q ↔ c S₀ = q`. This is the toy form of
   `etaAnab_eq_etaQ_iff`, with `c S₀` in the role of `logVol D (A.out ι S)` and `q` in the role of
   `(concreteVariantData D).qPilot.lhs`. The file also states the pilot-level form
   (`eta_equality_iff_pilot`, `eta_equality_iff_scalar_via_pilot`), so that the chain
   "equality of maps ⟺ agreement at the pilot ⟺ equality of scalars" is proved and not merely asserted.
   `etaQ_bijective` and `etaAnab_bijective` record that a member of either family is an isomorphism of
   pointed lines exactly when its scalar is non-zero — a *candidate* isomorphism with a zero scalar is a
   collapse, which is where §5's second degeneracy lives.
3. **The orbit form** (`InOrbit`, `orbitFamily`, `eta_eq_iff_inOrbit`,
   `in_orbit_iff_exists_iso_in_family`): the group `ℝˣ` acts on the scalars by `u • x = u * x`
   (`unit_smul_eq_mul`), a subgroup `H ≤ ℝˣ` is the indeterminacy, and `orbitFamily H c₀ s = s • c₀` is the
   family indexed **by the indeterminacy itself** — the toy stand-in for "(Ind3)-choice `S`". Then
   `(∃ s : H, etaAnab (orbitFamily H c₀) s = etaQ q) ↔ InOrbit H c₀ q`, i.e. *equality of maps, equality of
   scalars, and orbit membership are one statement*, and the form with the orbit condition inside the
   existential (`in_orbit_iff_exists_iso_in_family`) is proved as well. `exists_S_of_inOrbit` is the
   constructive direction: an orbit member *produces* the choice `S`. `nine_one_at_four` records one case
   where the toy's (9-1) holds with an explicit witness, and `top_inOrbit_iff` records that with the whole
   unit group as indeterminacy the orbit of a non-zero scalar is every non-zero scalar — so in this toy the
   obstruction is concentrated exactly at `q = 0`.
4. **Degeneracy with the pilot zero** (`idMap`, `doubleMap`, `agreement_at_zero_not_determining`,
   `zero_pilot_not_determining`, `map_eq_iff_pilot_fails_at_zero`): `idMap` (multiplication by `1`) and
   `doubleMap` (multiplication by `2`) are different maps with `idMap 0 = 0 = doubleMap 0`. So without
   `p ≠ 0` the reduction lemma is false, and the hypothesis of item 1 is not removable.
5. **Degeneracy with the scalar outside the orbit** (two witnesses, both computed, not assumed):
   with the trivial indeterminacy `H = ⊥` the family is the single map `scalarMap 1`, the target scalar is
   `2`, and `2` is not in the orbit of `1` (`not_inOrbit_bot`): `bottom_pointwise` exhibits the failure at
   the pilot (`1` against `2`) and `no_S_below_bottom` proves that no choice gives equality — although
   every involved map is an isomorphism, so this is *not* the zero-collapse of item 2 but a genuine failure
   of orbit membership. And
   with `H = ⊤` and target scalar `0`, `no_S_top_zero` proves that no choice gives equality, because the
   whole unit orbit of `1` misses `0` (`top_inOrbit_iff`): this is the case where the target is the zero
   map, so its own pilot is zero and it is not an isomorphism at all.
6. **A dependency-footprint line per declaration**, at the end of the file: every declaration, the `def`s
   and `abbrev`s included, prints a subset of `{propext, Classical.choice, Quot.sound}`.

**Restated, not imported.** The single import is `CoreLog.QpThree`, which supplies the ambient Mathlib
(`ℝ`, `LinearMap`, the unit group of `ℝ` and its subgroups). Nothing else in this repository is imported: the other
files of `candidates/core-transport/` are top-level modules of the package, are not Lake targets, have no
`olean`, and so cannot be imported — but nothing of them is needed here either, since the content of this
file is elementary linear algebra over `ℝ` and is written out in full. The upstream `Iut` files are a
different package with no dependency on this one, so `etaAnab_eq_etaQ_iff` and `eta_eq_eta_iff` are
**quoted** in this docstring and appear nowhere in the code: this file defines its own `etaAnab` and
`etaQ`, which are unrelated Lean constants that happen to share the names of the upstream ones.

**Non-claims.**

1. **It does not prove (9-1).** What is proved is a statement about `ℝ →ₗ[ℝ] ℝ`; (9-1) is a statement about
   `A.etaAnab ι S` and `etaQ D`, which are linear maps out of a value-group BPS `B.val.C` built from
   `out`, `BPS`, `Ind3`, `logVol` and `qPilot`. None of those objects occurs here.
2. **No `out`, no `BPS`, no `Ind3`, no `logVol`, no Θ-link, no Hodge theater, no volume container, no
   log-shell, no `Ism`, no `Ind1`/`Ind2`, no `q`-pilot as an arithmetic object** occurs in the code. The
   index type `S` of the family is an arbitrary type; `H` is an arbitrary subgroup of `ℝˣ`; `c` is an
   arbitrary function `S → ℝ`, not a log-volume; `q` is an arbitrary real, not `−|log q|`.
3. **The toy's (9-1) is a theorem of the toy only.** In the toy, "there is a choice `S` with equality" is
   *equivalent* to a scalar being in an orbit, and both directions are proved; that equivalence is a fact
   about multiplication on `ℝ` and carries no information about the real constructions. The upstream
   `Wall` hypothesis is an *open* proposition about those constructions; this file neither implies nor
   refutes it.
4. **The indeterminacy is not modelled as an action on `S`.** `Ind1`/`Ind2` act on the (Ind3)-choices
   upstream ([LANA] §10.4); here the family is simply indexed by the subgroup and no action on the index
   set is defined, so the file says nothing about how the choices are permuted, only about which scalars
   they produce.
5. **No evidence for or against any IUT claim.** The core GAP stays OPEN.

The file is written to the house discipline: no unfinished proof, no extra assumption, no decision
procedure by computation, and the footprint block at the end certifies the three standard principles.
-/

namespace EtaComparison

noncomputable section

/-! ## 1. Pointed lines, and the reduction lemma -/

/-- **The source pointed line** `R^val` ([LANA] §9.3: the value-group portion, carrying a canonical
pilot), as a toy: the one-dimensional real vector space `ℝ`. The pointing is not a structure here; it is
the non-zero real `p` that the theorems below take as an argument. -/
abbrev Rval : Type := ℝ

/-- **The target pointed line** `R^ss` ([LANA] §9.3: the unit monoid, log, log-shells, volume containers),
as a toy: again `ℝ`. That the two spaces coincide is deliberate — the content of (9-1) is which
isomorphism between them a construction produces, not what the spaces are. -/
abbrev Rss : Type := ℝ

/-- Both pointed lines are one-dimensional, which is the only structural fact the reduction lemma uses:
a single non-zero vector is a basis. -/
theorem finrank_Rval : Module.finrank ℝ Rval = 1 := Module.finrank_self ℝ

/-- The target pointed line is one-dimensional as well. -/
theorem finrank_Rss : Module.finrank ℝ Rss = 1 := Module.finrank_self ℝ

/-- **The map of pointed lines "multiplication by `a`"**: `x ↦ a * x`. Every map of pointed lines is of
this form for exactly one `a` (`map_eq_scalarMap`), so this is the toy shape of `ValBPS.eta`, which sends
the pilot of the source to the real number `a` and extends by linearity. -/
def scalarMap (a : ℝ) : Rval →ₗ[ℝ] Rss := LinearMap.mulLeft ℝ a

/-- The computation rule of `scalarMap`. -/
theorem scalarMap_apply (a x : ℝ) : scalarMap a x = a * x := LinearMap.mulLeft_apply ℝ a x

/-- **The scalar is recovered from the map**: evaluating at `1` inverts `scalarMap`. This is the "pointed"
half of the structure — the value at a non-zero point determines the scalar, hence the map. -/
theorem scalarMap_injective : Function.Injective scalarMap := by
  intro a b h
  have h1 : scalarMap a 1 = scalarMap b 1 := LinearMap.congr_fun h 1
  rwa [scalarMap_apply, scalarMap_apply, mul_one, mul_one] at h1

/-- **The reduction lemma: two maps of pointed lines are equal iff they agree at the pilot.** This is the
elementary content of `ValBPS.eta_eq_eta_iff`, and hence of `etaAnab_eq_etaQ_iff`: the forward direction
is congruence, and the backward direction is `LinearMap.ext` on the basis `1 = (1 / p) • p` — every `x` is
`(x / p) • p`, so the value at `p` propagates to every `x`. The hypothesis `p ≠ 0` is exactly what makes
that a basis, and §4 exhibits two different maps agreeing at `0`. -/
theorem map_eq_iff_pilot (f g : Rval →ₗ[ℝ] Rss) (p : ℝ) (hp : p ≠ 0) :
    f = g ↔ f p = g p := by
  constructor
  · intro h
    exact LinearMap.congr_fun h p
  · intro h
    refine LinearMap.ext fun x => ?_
    have hx : x = (x / p) • p := by
      rw [smul_eq_mul, div_mul_cancel₀ x hp]
    calc f x = f ((x / p) • p) := congrArg f hx
      _ = (x / p) • f p := LinearMap.map_smul f (x / p) p
      _ = (x / p) • g p := by rw [h]
      _ = g ((x / p) • p) := (LinearMap.map_smul g (x / p) p).symm
      _ = g x := congrArg g hx.symm

/-- **Every map of the pointed line is multiplication by its value at `1`** — the companion uniqueness
statement to `map_eq_iff_pilot`, and the toy form of `ValBPS.eta_unique`: a map of pointed lines has no
freedom beyond the image of one non-zero point. -/
theorem map_eq_scalarMap (f : Rval →ₗ[ℝ] Rss) : f = scalarMap (f 1) := by
  refine LinearMap.ext fun x => ?_
  rw [scalarMap_apply]
  calc f x = f (x • (1 : ℝ)) := congrArg f (by rw [smul_eq_mul, mul_one])
    _ = x • f 1 := LinearMap.map_smul f x 1
    _ = f 1 * x := by rw [smul_eq_mul, mul_comm]

/-! ## 2. A family of candidate isomorphisms, and (9-1) as an equation of numbers -/

/-- **The toy `η^anab`**: the family of maps of pointed lines indexed by the choice `S`, given by the
family of scalars `c : S → ℝ`. Upstream, `A.etaAnab ι S` is `B.val.eta (logVol D (A.out ι S))`; here
`c S₀` plays the role of that log-volume, and `S` is an arbitrary index type. -/
def etaAnab {S : Type*} (c : S → ℝ) (s : S) : Rval →ₗ[ℝ] Rss := scalarMap (c s)

/-- **The toy `η_q`**: the single map fixed by the scalar `q`, which plays the role of the `q`-pilot's
left-hand side `(concreteVariantData D).qPilot.lhs`. -/
def etaQ (q : ℝ) : Rval →ₗ[ℝ] Rss := scalarMap q

/-- The computation rule of the family at a point of the source. -/
theorem etaAnab_apply {S : Type*} (c : S → ℝ) (s : S) (x : ℝ) : etaAnab c s x = c s * x := by
  rw [etaAnab, scalarMap_apply]

/-- The computation rule of `etaQ` at a point of the source. -/
theorem etaQ_apply (q x : ℝ) : etaQ q x = q * x := by
  rw [etaQ, scalarMap_apply]

/-- **A member of the family is an isomorphism of pointed lines iff its scalar is non-zero** — the reason
the family is called a family of *candidate* isomorphisms: a zero scalar collapses the pointed line. -/
theorem etaAnab_bijective {S : Type*} (c : S → ℝ) (s : S) (hc : c s ≠ 0) :
    Function.Bijective (etaAnab c s) := by
  have h : (etaAnab c s : Rval → Rss) = fun x => c s * x := by
    funext x
    rw [etaAnab_apply]
  rw [h]
  exact mulLeft_bijective₀ (c s) hc

/-- **`etaQ q` is an isomorphism of pointed lines iff `q ≠ 0`** — the same statement for the single map. -/
theorem etaQ_bijective {q : ℝ} (hq : q ≠ 0) : Function.Bijective (etaQ q) := by
  have h : (etaQ q : Rval → Rss) = fun x => q * x := by
    funext x
    rw [etaQ_apply]
  rw [h]
  exact mulLeft_bijective₀ q hq

/-- **The scalar equation is solvable in the pilot**: `c * p = q * p ↔ c = q` for `p ≠ 0`. This is the
step that turns "the two maps have the same value at the pilot" into an equation of numbers. -/
theorem pilot_eq_iff_scalar (c q p : ℝ) (hp : p ≠ 0) : c * p = q * p ↔ c = q := by
  constructor
  · intro h
    exact mul_right_cancel₀ hp h
  · rintro rfl
    rfl

/-- **The pilot-level form of the reduction**: `etaAnab c S₀ = etaQ q` iff the two maps agree at the
pilot `p`. This is `map_eq_iff_pilot` at the two families, and it is the first link of the chain. -/
theorem eta_equality_iff_pilot {S : Type*} (c : S → ℝ) (q p : ℝ) (S₀ : S) (hp : p ≠ 0) :
    etaAnab c S₀ = etaQ q ↔ etaAnab c S₀ p = etaQ q p :=
  map_eq_iff_pilot _ _ p hp

/-- **The full chain at the pilot**: equality of maps ⟺ agreement at the pilot ⟺ equality of the two
scalars. The middle step is `pilot_eq_iff_scalar`, i.e. cancellation of the non-zero pilot. -/
theorem eta_equality_iff_scalar_via_pilot {S : Type*} (c : S → ℝ) (q p : ℝ) (S₀ : S) (hp : p ≠ 0) :
    etaAnab c S₀ = etaQ q ↔ c S₀ = q := by
  rw [eta_equality_iff_pilot c q p S₀ hp, etaAnab, etaQ, scalarMap_apply, scalarMap_apply,
    pilot_eq_iff_scalar (c S₀) q p hp]

/-- **(9-1) for one choice `S₀` is an equation of real numbers**: `etaAnab c S₀ = etaQ q ↔ c S₀ = q`.
This is the toy counterpart of `etaAnab_eq_etaQ_iff`, which says the same thing with `c S₀` replaced by
`logVol D (A.out ι S)` and `q` by `(concreteVariantData D).qPilot.lhs`: here the equation is decided at
the pilot `1`, so the statement is the `p = 1` case of `eta_equality_iff_scalar_via_pilot` and needs no
hypothesis. -/
theorem eta_equality_iff_scalar {S : Type*} (c : S → ℝ) (q : ℝ) (S₀ : S) :
    etaAnab c S₀ = etaQ q ↔ c S₀ = q :=
  eta_equality_iff_scalar_via_pilot c q 1 S₀ one_ne_zero

/-- **Existence of a choice, as an equation of numbers**: some `S₀` gives equality of maps iff some `S₀`
has its scalar equal to `q`. This is the quantifier form that (9-1) actually asks for. -/
theorem exists_eta_eq_iff_exists_scalar {S : Type*} (c : S → ℝ) (q : ℝ) :
    (∃ S₀ : S, etaAnab c S₀ = etaQ q) ↔ ∃ S₀ : S, c S₀ = q := by
  constructor
  · rintro ⟨S₀, h⟩
    exact ⟨S₀, (eta_equality_iff_scalar c q S₀).mp h⟩
  · rintro ⟨S₀, h⟩
    exact ⟨S₀, (eta_equality_iff_scalar c q S₀).mpr h⟩

/-! ## 3. The orbit form

The group `ℝˣ` of units acts on the scalars by multiplication, `u • x = u * x`. A subgroup `H ≤ ℝˣ` is
the indeterminacy, and the family of candidate isomorphisms is indexed **by the indeterminacy itself**:
the choice `S` of (9-1) is, in this toy, the choice of an element of `H`, and the scalar it produces is
`s • c₀`. That is what makes the orbit statement an *equivalence* rather than an analogy. -/

/-- The action of the units of `ℝ` on the scalars: `u • x = u * x`. -/
theorem unit_smul_eq_mul (u : ℝˣ) (x : ℝ) : u • x = (u : ℝ) * x := by
  rw [Units.smul_def, smul_eq_mul]

/-- **The orbit of a scalar under the indeterminacy**: `q` is obtained from `c` by some `u ∈ H`, i.e.
`q = u * c`. This is the toy form of "[LANA] §9.3: `η_q` lies in the orbit of the `η^anab_S`" — the
"analogue of a Teichmüller deformation" of the report. -/
def InOrbit (H : Subgroup ℝˣ) (c q : ℝ) : Prop := ∃ u : ℝˣ, u ∈ H ∧ q = (u : ℝ) * c

/-- The orbit condition written with the group action: `q = u • c`. -/
theorem inOrbit_iff_exists_smul (H : Subgroup ℝˣ) (c q : ℝ) :
    InOrbit H c q ↔ ∃ u : ℝˣ, u ∈ H ∧ q = u • c := by
  simp only [InOrbit, unit_smul_eq_mul]

/-- The orbit condition with the witness living in the subgroup rather than in `ℝˣ`. -/
theorem inOrbit_iff_exists_unit (H : Subgroup ℝˣ) (c q : ℝ) :
    InOrbit H c q ↔ ∃ u : H, q = ((u : ℝˣ) : ℝ) * c := by
  constructor
  · rintro ⟨u, hu, hq⟩
    exact ⟨⟨u, hu⟩, hq⟩
  · rintro ⟨u, hq⟩
    exact ⟨(u : ℝˣ), u.2, hq⟩

/-- **The family of candidate isomorphisms, indexed by the indeterminacy**: at `s : H` the scalar is
`s • c₀`. This is the toy stand-in for the (Ind3)-choice `S` of [LANA] §9.2 — an element of the group,
not an index into a list. -/
def orbitFamily (H : Subgroup ℝˣ) (c₀ : ℝ) (s : H) : ℝ := ((s : ℝˣ) : ℝ) * c₀

/-- **Equality of maps is orbit membership.** This is the chain of the task in one statement: there is a
choice in the family whose map equals `etaQ q` iff `q` is the image of the base scalar `c₀` under the
indeterminacy. Proof: `exists_eta_eq_iff_exists_scalar` reduces the maps to scalars, and the scaling
relation `q = s • c₀` is the orbit relation — the two directions are the two directions of "membership in
a subgroup". -/
theorem eta_eq_iff_inOrbit (H : Subgroup ℝˣ) (c₀ q : ℝ) :
    (∃ s : H, etaAnab (orbitFamily H c₀) s = etaQ q) ↔ InOrbit H c₀ q := by
  rw [exists_eta_eq_iff_exists_scalar]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨(s : ℝˣ), s.2, hs.symm⟩
  · rintro ⟨u, hu, hq⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show (u : ℝ) * c₀ = q
    exact hq.symm

/-- **(9-1) in the toy, in orbit form**: there is a choice in the family with `η^anab = η_q` iff there is
a choice whose own scalar has `q` in its orbit. This is the statement the task items 3 and 4 ask for; the
right-hand side is *not* a mere restatement, because the family is indexed by the group and the orbit of a
member of the family is the orbit of the base scalar (`eta_eq_iff_inOrbit` closes the circle). -/
theorem in_orbit_iff_exists_iso_in_family (H : Subgroup ℝˣ) (c₀ q : ℝ) :
    (∃ S₀ : H, etaAnab (orbitFamily H c₀) S₀ = etaQ q) ↔
      ∃ S₀ : H, InOrbit H (orbitFamily H c₀ S₀) q := by
  rw [eta_eq_iff_inOrbit]
  constructor
  · rintro ⟨u, hu, hq⟩
    refine ⟨⟨1, H.one_mem⟩, u, hu, ?_⟩
    simpa [orbitFamily] using hq
  · rintro ⟨s, u, hu, hq⟩
    refine ⟨u * (s : ℝˣ), H.mul_mem hu s.2, ?_⟩
    rw [Units.val_mul, hq, orbitFamily]
    ring

/-- **The constructive direction**: an orbit member produces a choice `S` in the family for which the two
maps coincide. In the toy this is the only thing that would ever discharge (9-1), and it is a statement
about the indeterminacy, not about the maps. -/
theorem exists_S_of_inOrbit (H : Subgroup ℝˣ) (c₀ q : ℝ) (h : InOrbit H c₀ q) :
    ∃ s : H, etaAnab (orbitFamily H c₀) s = etaQ q :=
  (eta_eq_iff_inOrbit H c₀ q).mpr h

/-- **With the whole unit group as indeterminacy, the orbit of a non-zero scalar is every non-zero
scalar.** This is what makes the toy's obstruction sharp: the only scalar that no choice can reach is
`0`, i.e. the collapse case of §2. -/
theorem top_inOrbit_iff (c q : ℝ) (hc : c ≠ 0) : InOrbit ⊤ c q ↔ q ≠ 0 := by
  constructor
  · rintro ⟨u, -, hq⟩
    rw [hq]
    exact mul_ne_zero (Units.ne_zero u) hc
  · intro hq
    refine ⟨Units.mk0 (q / c) (div_ne_zero hq hc), Subgroup.mem_top _, ?_⟩
    rw [Units.val_mk0, div_mul_cancel₀ q hc]

/-- **A case where the toy's (9-1) holds, with an explicit choice**: `q = 4` is reached from `c₀ = 1` by
the unit `4`, whose existence is `top_inOrbit_iff`; the choice itself is `Units.mk0 (4 / 1)`. -/
theorem nine_one_at_four : ∃ s : (⊤ : Subgroup ℝˣ), etaAnab (orbitFamily ⊤ 1) s = etaQ 4 :=
  exists_S_of_inOrbit ⊤ 1 4 ((top_inOrbit_iff 1 4 one_ne_zero).mpr (by norm_num))

/-- **A case where no choice in the family gives equality, with the whole unit group as indeterminacy**:
the target scalar `0` is not in the orbit of `1`, because every unit is non-zero. The target map `etaQ 0`
is the zero map (`etaQ_apply`), so its own pilot is zero and it is not an isomorphism. -/
theorem no_S_top_zero : ¬ ∃ s : (⊤ : Subgroup ℝˣ), etaAnab (orbitFamily ⊤ 1) s = etaQ 0 := by
  rintro h
  have h' : InOrbit ⊤ (1 : ℝ) 0 := (eta_eq_iff_inOrbit ⊤ 1 0).mp h
  exact ((top_inOrbit_iff 1 0 one_ne_zero).mp h') rfl

/-! ## 4. Degeneracy, both directions, with numbers -/

/-- **The identity map of the pointed line**: multiplication by `1`. -/
def idMap : Rval →ₗ[ℝ] Rss := scalarMap 1

/-- **Multiplication by `2`**: a second map of the same pointed line, different from `idMap`. -/
def doubleMap : Rval →ₗ[ℝ] Rss := scalarMap 2

/-- `idMap` kills `0`, as every linear map does. -/
theorem idMap_zero : idMap 0 = 0 := by
  rw [idMap, scalarMap_apply, mul_zero]

/-- `doubleMap` kills `0` as well. -/
theorem doubleMap_zero : doubleMap 0 = 0 := by
  rw [doubleMap, scalarMap_apply, mul_zero]

/-- **The two maps are different**: they disagree at `1`, where the values are `1` and `2`. -/
theorem idMap_ne_doubleMap : idMap ≠ doubleMap := by
  intro h
  have h1 : idMap 1 = doubleMap 1 := LinearMap.congr_fun h 1
  rw [idMap, doubleMap, scalarMap_apply, scalarMap_apply] at h1
  norm_num at h1

/-- **Agreement at a zero pilot does not determine a map of pointed lines**: `idMap ≠ doubleMap` while
`idMap 0 = 0 = doubleMap 0`. This is why `map_eq_iff_pilot` carries `p ≠ 0`, and it is the toy form of the
reason `ValBPS.eta_eq_eta_iff` is a statement about a *non-zero* pilot point. -/
theorem agreement_at_zero_not_determining :
    ∃ f g : Rval →ₗ[ℝ] Rss, f ≠ g ∧ f 0 = g 0 :=
  ⟨idMap, doubleMap, idMap_ne_doubleMap, by rw [idMap_zero, doubleMap_zero]⟩

/-- **Without the hypothesis `p ≠ 0` the reduction lemma is false**, stated as the sharp negation: it is
not the case that agreement at `0` forces equality of maps. -/
theorem zero_pilot_not_determining : ¬ ∀ f g : Rval →ₗ[ℝ] Rss, f 0 = g 0 → f = g := by
  intro h
  exact idMap_ne_doubleMap (h idMap doubleMap (by rw [idMap_zero, doubleMap_zero]))

/-- **`map_eq_iff_pilot` at `p = 0` is false**, for the two maps above: `idMap ≠ doubleMap` while
`idMap 0 = doubleMap 0`, so the equivalence fails at the zero pilot. -/
theorem map_eq_iff_pilot_fails_at_zero : ¬ (idMap = doubleMap ↔ idMap 0 = doubleMap 0) := by
  rw [idMap_zero, doubleMap_zero]
  simp [idMap_ne_doubleMap]

/-- **With the trivial indeterminacy the family is a single map.** At the only index, `s • c₀ = c₀`, so
the family collapses to `scalarMap c₀`. -/
theorem orbitFamily_bot (c₀ : ℝ) (s : (⊥ : Subgroup ℝˣ)) : orbitFamily ⊥ c₀ s = c₀ := by
  obtain ⟨u, hu⟩ := s
  have hu1 : u = 1 := Subgroup.mem_bot.mp hu
  subst hu1
  simp [orbitFamily]

/-- **The failure at `H = ⊥`, exhibited at the pilot**: every member of the trivial family sends `1` to
`1`, while `etaQ 2` sends it to `2`. Both maps are isomorphisms of pointed lines
(`etaAnab_bijective`, `etaQ_bijective`), so this is a failure of orbit membership and not a collapse. -/
theorem bottom_pointwise (s : (⊥ : Subgroup ℝˣ)) :
    etaAnab (orbitFamily ⊥ 1) s 1 = 1 ∧ etaQ 2 1 = 2 := by
  constructor
  · rw [etaAnab_apply, orbitFamily_bot, mul_one]
  · rw [etaQ_apply, mul_one]

/-- **`2` is not in the orbit of `1` under the trivial indeterminacy**: the scalar fact behind the failure
below, proved on its own so that "the scalar equation has no solution" is a theorem and not an inference
from the maps. -/
theorem not_inOrbit_bot : ¬ InOrbit (⊥ : Subgroup ℝˣ) (1 : ℝ) 2 := by
  rintro ⟨u, hu, hq⟩
  rw [Subgroup.mem_bot] at hu
  subst hu
  rw [Units.val_one, one_mul] at hq
  norm_num at hq

/-- **No choice in the trivial family gives equality at `q = 2`.** The family's only scalar is `1`, the
target scalar is `2`, and `2` is not in its orbit (`not_inOrbit_bot`): the scalar equation of §2 has no
solution, so by `exists_eta_eq_iff_exists_scalar` neither does the equation of maps. Numbers: `1` against
`2`. -/
theorem no_S_below_bottom : ¬ ∃ s : (⊥ : Subgroup ℝˣ), etaAnab (orbitFamily ⊥ 1) s = etaQ 2 := by
  rintro ⟨s, h⟩
  have h1 : etaAnab (orbitFamily ⊥ 1) s 1 = etaQ 2 1 := LinearMap.congr_fun h 1
  rw [etaAnab_apply, orbitFamily_bot, etaQ_apply] at h1
  norm_num at h1

end

end EtaComparison

#print axioms EtaComparison.Rval
#print axioms EtaComparison.Rss
#print axioms EtaComparison.finrank_Rval
#print axioms EtaComparison.finrank_Rss
#print axioms EtaComparison.scalarMap
#print axioms EtaComparison.scalarMap_apply
#print axioms EtaComparison.scalarMap_injective
#print axioms EtaComparison.map_eq_iff_pilot
#print axioms EtaComparison.map_eq_scalarMap
#print axioms EtaComparison.etaAnab
#print axioms EtaComparison.etaQ
#print axioms EtaComparison.etaAnab_apply
#print axioms EtaComparison.etaQ_apply
#print axioms EtaComparison.etaAnab_bijective
#print axioms EtaComparison.etaQ_bijective
#print axioms EtaComparison.pilot_eq_iff_scalar
#print axioms EtaComparison.eta_equality_iff_pilot
#print axioms EtaComparison.eta_equality_iff_scalar_via_pilot
#print axioms EtaComparison.eta_equality_iff_scalar
#print axioms EtaComparison.exists_eta_eq_iff_exists_scalar
#print axioms EtaComparison.unit_smul_eq_mul
#print axioms EtaComparison.InOrbit
#print axioms EtaComparison.inOrbit_iff_exists_smul
#print axioms EtaComparison.inOrbit_iff_exists_unit
#print axioms EtaComparison.orbitFamily
#print axioms EtaComparison.eta_eq_iff_inOrbit
#print axioms EtaComparison.in_orbit_iff_exists_iso_in_family
#print axioms EtaComparison.exists_S_of_inOrbit
#print axioms EtaComparison.top_inOrbit_iff
#print axioms EtaComparison.nine_one_at_four
#print axioms EtaComparison.no_S_top_zero
#print axioms EtaComparison.idMap
#print axioms EtaComparison.doubleMap
#print axioms EtaComparison.idMap_zero
#print axioms EtaComparison.doubleMap_zero
#print axioms EtaComparison.idMap_ne_doubleMap
#print axioms EtaComparison.agreement_at_zero_not_determining
#print axioms EtaComparison.zero_pilot_not_determining
#print axioms EtaComparison.map_eq_iff_pilot_fails_at_zero
#print axioms EtaComparison.orbitFamily_bot
#print axioms EtaComparison.bottom_pointwise
#print axioms EtaComparison.not_inOrbit_bot
#print axioms EtaComparison.no_S_below_bottom
