# Primitive deck action and canonical cusp class (model level)

Date: 2026-10-25. Base branch:
`autonomous/theta-triple-product-20261025` at
`cf51cdc1e8d65e53591048ef4120884bf9c5bc36`.

## Why this target

The project's own `GAP-original-source.md` names six source obligations; the
three the user picked are:

1. the theta line bundle `L_N`, section `s₁`, trivialization `τ_N`, root
   torsors;
2. the primitive deck generator = `q`-translation;
3. canonical cusp parameters.

Three of the ten fan-out reviewers independently established that (1) has no
host in the current dependency layer: `L_N`, `τ_N` and root torsors are absent,
and the upstream scope record itself blames the missing structure sheaf on
infinite covers. A `structure` holding the desired trivialization would be a
field smuggling the conclusion, so (1) is **not** attempted here.

Reviewers disagreed only on how much of (2) and (3) is statable. The resolution
adopted here: build the `ℤ`-action and the quotient first, then the cusp is a
class in that quotient rather than a point of `Kˣ` (there is no fixed point of
`ℤ` on `Kˣ`, so a representative-level "canonical cusp" would be false).

## Results

`candidates/core-kummer/Boundary/PrimitiveDeck.lean`, namespace
`CorePrimitiveDeck`. Over `t : TateParameter K`:

| theorem | statement |
|---|---|
| `q_zpow_ne_one` | `m ≠ 0 → (q : Kˣ)^m ≠ 1` |
| `deck_action_free` | `q^m * u = u → m = 0` |
| `zpow_injective` | `m ↦ (q : Kˣ)^m` is injective |
| `deck_generator_infinite_order` | `0 < n → (q : Kˣ)^n ≠ 1` |
| `deckRel_refl/symm/trans` | the deck relation is an equivalence |
| `deckOrbitEquiv` | `ℤ ≃ {v // deckRel t u v}`, i.e. orbits are `ℤ`-torsors |
| `deck_automorphy` | `theta (q^m·u) = (q^(e m)·u^m)⁻¹ · theta u` |
| `theta_zero_iff_deck_orbit` | `theta u = 0 ↔ deckRel t (-1) u` |
| `theta_zero_descends_to_quotient` | vanishing is a deck-class invariant |
| `theta_zero_iff_eq_cuspClass` | `theta u = 0 ↔ [u] = cuspClass` |
| `theta_zero_orbit_unique` | any two zeros lie in one deck class |

Definitions: `deckRel`, `deckSetoid`, `DeckQuotient` (the model `Kˣ/qᶻ`),
`cuspClass` (the class of `-1`).

The primitivity statement is *proved*, not assumed: `TateParameter.pow_ne_one`
already gives that `q` is not a root of unity, which forces the action to be
free and the generator to have infinite order. No surjectivity, no
`Π^tp_X / Π^tp_Y ≃ ℤ` hypothesis and no choice of an abstract generator enters.

## Verification

From a clean clone of the branch, with `-DwarningAsError=true`:

```powershell
cd candidates/core-kummer
lake build Boundary.PrimitiveDeck
lake env lean -DwarningAsError=true Boundary/PrimitiveDeck.lean
```

Result: `Build completed successfully (2760 jobs)`; the twelve `#print axioms`
lines all report exactly `[propext, Classical.choice, Quot.sound]`. A previous
intermediate state did contain `sorryAx`; that state was never committed and
the final build was re-run from source.

## Adversarial review points that shaped the statement

- **Cusp cannot be a point of `Kˣ`.** `ℤ` acts freely on `Kˣ`, so there is no
  invariant representative; `u = 0` is not in the domain of `theta`. Hence the
  cusp is defined as `cuspClass : DeckQuotient t`, and the "canonical" content
  is the uniqueness theorem `theta_zero_iff_eq_cuspClass`, not a label.
- **`DeckQuotient` must not be called `E_q`.** No Weierstrass equation, no
  group law and no integral model is attached; it is the coordinate quotient
  only.
- **`k` in `theta u = 0 ↔ ∃ k, u = -q^k` is not a canonical exponent** (the
  witness set is a coset, and `e 0 = e (-1)` degenerates). The file never uses
  `k` after projecting to `deckRel`; only the class survives.
- **The `q` vs `-q` symmetry** (`theta_{-q}(u) = theta_q(-u)`) means the model
  modulus does not distinguish them; no claim of an absolute normalization is
  made.
- **`cuspClass ≠ [1]` needs `(2 : K) ≠ 0` and is not proved here.** Three
  reviewers converged on this: in characteristic `2`, `1 = -1`, so the two
  representatives coincide. `one_ne_neg_one` records the field-level half
  (`[CharZero K] → (1 : K) ≠ -1`); the quotient-level distinctness is left as
  an explicit gap rather than assumed. The verified content is the *labelled*
  zero class, not a certified second point of the quotient.
- **README wording** was narrowed accordingly: it no longer claims to
  "discharge two of the three source boundaries".

## Boundaries (unchanged)

- Not the original tempered covering, not `Π^tp_Y`, not `L_N`, `s₁` or `τ_N`.
- No identification of the model generator with the original IUT
  `q`-translation; `TemperedCovering` only gives an abstract `ℤ` quotient, and
  `n = 1` is explicitly not available there.
- Not Corollary 3.12, not (9-1), not abc.
- No VS Code editor observation, no fact-tree or central registry admission.
