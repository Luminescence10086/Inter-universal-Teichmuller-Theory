# Read-only selection review of the integrated tool candidates

Review date: 2026-10-20. Scope: current saved `ScaleLedger`, `Admissibility`,
`Slots`, `WeightedLedger`, and `Integration` sources. No source file was modified
for this review; no UI receipt, fact-tree admission, or new compilation of the
other agent's modules is claimed. After the read-only review, the parent
explicitly requested two additional Integration wrappers; those were added
without modifying the original seven declarations. All nine passed the final
warning-as-error CLI check recorded in `RESULTS.md`.

## Selected interfaces

| Tool family | Retain as the precise reusable result | Limit on its use |
| --- | --- | --- |
| `ScaleLedger.layer_subset_of_le`, `layer_ssubset_of_lt`, `cost_exact`, `composeShift_eq_shift_sum` | Strictly antitone norm balls; exact set-image transport by the signed exponent difference; finite-chain composition by exponent sum | No cost function, measure, volume, or optimality; widening moves toward smaller indices |
| `Admissibility.rectangular_iff_product`, `not_rectangular_of_graph`, `rectangular_subrelation_freezes_layer` | A test for replacing a joint relation by independent marginals; a graph obstruction; any two realized layers of a rectangular subrelation agree | Applying it to an IUT relation requires constructing that relation and proving the relevant graph/subrelation hypotheses |
| `Admissibility.frozen_isRectangular`, `frozen_sigma_marginal` | Every fixed target layer `c` gives a rectangular relation, with a witness at `c` | The second current declaration proves existence at `c`, not a universally quantified marginal iff; no existence is supplied for an arbitrary rectangular subrelation |
| `Integration.frozen_sigma_marginal_iff`, `rectangular_nonempty_unique_layer` | The full fixed-layer marginal iff; a nonempty rectangular subrelation realizes exactly one layer | Unique existence requires the explicit nonempty witness, in addition to the subrelation and rectangularity hypotheses |
| `Integration.slotwise_commutes_iff`, `Slots.relabel_slotwise` | Complete diagonal commutation criterion and the exact transported scalar family | The criterion quantifies only slotwise scalar maps, not arbitrary linear maps |
| `Slots.mixingEquiv_commutes_swap`, `mixingMap_not_slotwise`, inverse and linearity laws | A concrete invertible non-diagonal linear map commuting with a nontrivial swap | Existence of one such map does not establish preservation of a lattice, ledger, seed region, or actual IUT admissibility |
| `WeightedLedger.weightedLedger_invariant_iff`, `totalLedger_relabel` | Pure relabelling preserves every tuple's weighted ledger iff its weights are invariant; the unweighted sum always is | These concern arbitrary integer weights on abstract finite slots |
| `Integration.weightedLedger_relabel_slotwise`, both combined invariance iffs, support formula | Exact ledger transformation and sharp criteria on two distinct input domains | Scalars must be coordinatewise nonzero; actual admissible input regions may be smaller than either quantified domain |
| `WeightedLedger.pilotWeights_not_invariant`, `pilotLedger_not_invariant` | Sanity-check examples for the toy vector `(1,1,2,1)` | These weights have no proved identification with an IUT packet's actual weights |
| `WeightedLedger.norm_prod_eq_zpow_totalLedger` | Product of element norms equals `p` to the negative unweighted valuation sum, on coordinatewise nonzero tuples | It is not a measure-volume theorem, not a statement about arbitrary weights, and not a log-volume estimate |

Auxiliary lemmas such as delta-profile evaluation, nonzero probes, sum
reindexing, and mixing-map linearity should remain available as proof support.
They need not be advertised as additional independent mathematical discoveries.

## Checks on frozen layers and mixing

The proof of `frozen_isRectangular c` correctly substitutes equality of the two
fixed target indices; it works for any integer `c`. The witness in
`frozen_sigma_marginal c` is the actual map `shift p c`. Nothing here forces the
chosen target layer to be zero.

“Frozen target layer” means `e '' ball = layer c`. It must not be silently read
as `e '' layer c = layer c`, as “all automorphisms are now allowed”, or as
preservation of any further region. The rectangular-subrelation theorem takes
two existing relation witnesses; an empty relation satisfies it vacuously.
The new `Integration.rectangular_nonempty_unique_layer` upgrades this to unique
existence only after adding an explicit nonemptiness premise. The new
`Integration.frozen_sigma_marginal_iff` states the full all-`k` fixed-layer iff,
using the actual dilation as its existence witness.

The mixing example is `(x₀,x₁) ↦ (2x₀+x₁, x₀+2x₁)`, with the explicit
one-third inverse. Its inverse is valid even at `p = 3`, because `Q_p` has
characteristic zero. Invertibility over `Q_p` does not imply integrality of the
inverse or preservation of the product unit ball. The commutation proof is
coordinatewise algebra; non-slotwise behavior is detected on a basis tuple.

There is no conflict with `slotwise_commutes_iff`: that iff has a narrower map
type. Likewise, one cannot substitute `mixingEquiv` into the diagonal ledger
formula. Addition of coordinates introduces cancellation and may create zeros.
For example, direct algebra gives `T(1,-2) = (0,-3)`; this explanatory computation
is not an additional Lean declaration or admission claim.

## The nonzero domain matters

Write `T(x) = relabel σ (slotwise a x)` and assume every `a j` is nonzero.

| Quantified inputs | Exact criterion already proved |
| --- | --- |
| Every `x` with **each coordinate** nonzero | `w (σ j) = w j` for every `j`, and `Σ j, w j * v(a j) = 0` |
| Every `x`, allowing zero coordinates | `w (σ j) = w j` for every `j`, and `w j * v(a j) = 0` for every `j` |

“The vector is nonzero” is weaker than “each coordinate is nonzero” and is not
the first theorem's domain. Mathlib's integer-valued `Padic.valuation` assigns
`0` to the element `0`; this is why the support formula drops scalar budgets
at zero input coordinates.

The converse on the coordinatewise nonzero domain uses the constant-one tuple
and delta probes with entries `p` and `1`. The all-tuples converse additionally
uses single-coordinate probes with entries `1` and `0`. If an intended IUT input
region does not contain these probes, global ledger preservation on that region
does not automatically imply the same necessary conditions. The sufficient
directions remain available wherever their explicit input conditions hold.

Integer weights can be zero or negative. In particular, the all-tuples
criterion does not force `v(a j) = 0` at a zero-weight slot. No positivity,
averaging normalization, or inequality follows from the definitions alone.
Commuting operators and preserving the weighted ledger are different
properties: scalar-family invariance is not the same condition as
weight-family invariance plus a budget equation.

## Norm products are not measure volumes

The norm-product theorem concerns a finite product of real numbers `‖x j‖`.
There is no measurable region, chosen Haar measure, normalization, determinant
scaling theorem, or Arakelov contribution in its statement or proof. A base-`p`
logarithm of that positive product would have the **negative** of the unweighted
total ledger; even this logarithmic reformulation is not the theorem currently
stated.

With any zero coordinate, the norm product is zero but `p` to a finite integer
power remains positive. Thus dropping the coordinatewise nonzero premise
would make the displayed norm-product identity false. Pure relabelling ledger
identities do permit zeros; that fact cannot remove the norm theorem's premise.

To obtain a volume statement one must define the intended measurable regions
and measure, fix normalization, prove their transformation law, and connect
those regions to the actual comparison. A relation between a norm product and
the volume of a separately defined product region would itself require proof.

## Outstanding IUT uses and obligations

1. **Represent actual data.** Define the intended local objects, allowed
   transformations, slot set, and weights; construct maps into this finite
   `Q_p` model and prove they respect the structures that the comparison uses.
   The present model does not construct Ism/Kummer elements or prove that their
   actions are `Q_p`-linear, diagonal, or described by these permutations.
2. **Keep joint admissibility.** Build the actual joint relation and its
   witnesses. Use the rectangularity tools only after proving a graph or
   subrelation correspondence; matching separate marginals alone cannot supply
   the required joint lift or seed-region membership.
3. **Audit synchronization and weights.** If the action is proved diagonal,
   apply the scalar commutation criterion and the exact ledger transformation.
   Identify the actual input domain before using either necessity direction.
   For mixing actions, prove separate transformation and admissibility results.
4. **Provide arithmetic interfaces.** Any passage to ramified extensions,
   different valuation normalizations, `log_p` images, or actual local packets
   requires additional definitions and bridge proofs. The base-field lemmas do
   not supply those interfaces.
5. **Provide quantitative estimates.** Define the relevant measure or
   Arakelov quantity and prove the required scaling and comparison bounds.
   Neither `cost_exact` nor the norm-product identity supplies an enlargement
   cost estimate, Step (v), Corollary 3.12, or abc.

These are uses for checking a proposed construction, not completed obligations.

## Wording issues found in the reviewed snapshot

- `WeightedLedger.lean:199-200` calls the norm-product identity a precise sense
  of “log-volume”. Replace this with “norm-product identity / valuation-sum
  identity”; retain an explicit statement that no measure-volume is defined.
- `Admissibility.lean:193-198` describes `frozen_sigma_marginal` as the exact
  singleton marginal, while its declaration proves only membership at `c`.
  Narrow the description or separately prove the all-`k` iff. Catalog the actual
  declaration, not the stronger prose.
- `ScaleLedger.lean:69-71` says valuation is only defined on nonzero elements.
  Say instead that this valuation characterization requires nonzero input;
  Mathlib's valuation itself is total.
- `ScaleLedger.lean:166` says “Strict monotonicity”; the precise direction here
  is strict antitonicity.

These observations were sent to the source owner. The statements and proofs
reviewed do not rely on the stronger wording. Line numbers refer to the saved
snapshot read for this review and may move after owner edits.
