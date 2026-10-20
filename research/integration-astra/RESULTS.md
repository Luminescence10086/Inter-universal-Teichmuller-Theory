# Integration candidate: exact combined ledger criteria

Owned source: `bridge/IUTBridge/Integration.lean` only. No change to the root
import, theorem catalog, original modules, UI receipts, or fact-tree admission.

The current `Slots.lean` already contains the invertible non-diagonal mixing
example, its inverse laws, commutation with the swap, and non-slotwise property.
This candidate reuses the diagonal interface and does not duplicate that work.

## Mathematical scope and review

All statements concern arbitrary integer weights on abstract `Fin n` slots and
actual `Q_p`. They establish no IUT construction, volume statement, abc estimate,
or novelty claim. `WeightedLedger.lean` was read and left unchanged.

The weighted ledger's delta probe has value `p` at its distinguished coordinate
and value `1` elsewhere. Every coordinate is therefore nonzero. Together with
the constant-one tuple it proves the converse of combined preservation without
assuming that `n` is positive:

- The constant-one tuple forces the transported total scaling budget to vanish.
- The delta probes recover every transported weight.
- Invariant weights then identify the transported budget with the original one.

The sharp distinction is between **coordinatewise nonzero tuples** and **all
tuples**. A merely nonzero vector may still have zero coordinates and does not
satisfy the first criterion's input condition. For all tuples, a tuple with a
single coordinate equal to `1` and all other coordinates zero isolates each
scalar budget. Thus cancellation among different coordinates suffices only on
the coordinatewise nonzero locus.

All scalar families in the ledger transformation criteria are explicitly
coordinatewise nonzero. This is the setting of invertible diagonal scaling.
Zero scalar families are not covered by these criteria. The diagonal
commutation iff itself has no nonzero restriction.

## Catalog declarations and explicit non-typeclass Prop premises

Every name below has prefix `IUTBridge.Integration.`. The typeclass assumption
`[Fact p.Prime]` is present throughout; it is not an explicit Prop premise.

| Declaration | Explicit non-typeclass Prop premises |
| --- | --- |
| `slotwise_commutes_iff` | none |
| `deltaTuple_ne_zero` | none |
| `weightedLedger_relabel_slotwise` | `ha : ∀ j, a j ≠ 0`; `hx : ∀ j, x j ≠ 0` |
| `weightedLedger_combined_invariant_iff` | `ha : ∀ j, a j ≠ 0` |
| `exists_combined_ledger_failure` | `ha : ∀ j, a j ≠ 0`; `hfailure : (∃ j, w (σ j) ≠ w j) ∨ (∑ j, w j * (a j).valuation) ≠ 0` |
| `weightedLedger_relabel_slotwise_support` | `ha : ∀ j, a j ≠ 0` |
| `weightedLedger_combined_invariant_all_iff` | `ha : ∀ j, a j ≠ 0` |
| `frozen_sigma_marginal_iff` | none |
| `rectangular_nonempty_unique_layer` | `hsub : ∀ (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int), R e k → IUTBridge.Admissibility.LatticeAdmissible p e k`; `hrect : IUTBridge.Admissibility.IsRectangular R`; `hne : ∃ (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (k : Int), R e k` |

The nonzero input condition inside the first preservation iff belongs to the
quantified property being characterized, not to the declaration's outer
telescope. In the existential failure theorem the disjunction is a substantive
failure certificate; the existential witness is derived from the proved iff.

### Public catalog selection

All nine public Integration theorems in the table above are suitable for
catalog entries with exactly the listed outer premises and their actual
statements. `deltaTuple_ne_zero` is a supporting lemma; the other eight provide
the combined-action API, its failure certificate, or precise frozen-layer
interfaces. This recommendation
does not mark entries accepted by any separate UI/fact-tree workflow.

For the other agent's added public declarations, the current source supports
the following additional catalog candidates:

| Namespace and public theorem | Explicit non-typeclass Prop premises | Exact catalog scope |
| --- | --- | --- |
| `Admissibility.frozen_isRectangular` | none | Rectangularity at arbitrary fixed target layer `c` |
| `Admissibility.frozen_sigma_marginal` | none | A witness at the fixed target layer `c`; no all-`k` iff in its current statement |
| `Slots.mixingMap_add` | none | Additivity of the explicit mixing map |
| `Slots.mixingMap_smul` | none | `Q_p` homogeneity of the explicit mixing map |
| `Slots.mixingInv_left` | none | Explicit left inverse law |
| `Slots.mixingInv_right` | none | Explicit right inverse law |
| `Slots.mixingEquiv_commutes_swap` | none | The explicit linear equivalence commutes with the two-slot swap |
| `Slots.mixingMap_not_slotwise` | none | The explicit map cannot equal any slotwise scalar action on every tuple |

All names in this table have prefix `IUTBridge.`. Prime typeclass assumptions
are not explicit Prop premises. `mixingMap`, `mixingInv`, and `mixingEquiv` are
definitions rather than theorems. Their mathematical names should not be
inserted into a theorem-only catalog as though they were proof declarations.

`WeightedLedger.norm_prod_eq_zpow_totalLedger` may be cataloged with the
explicit premise `hx : ∀ j, x j ≠ 0`, and described only as the product-of-norms
identity. The pure relabelling invariance theorems have no such premise.
`WeightedLedger.weightedLedger_slotwise` has both
`ha : ∀ j, a j ≠ 0` and `hx : ∀ j, x j ≠ 0`;
`weightedLedger_uniform` has only the latter. These domains must not be merged.
Other WeightedLedger declarations are already enumerated by that module's
owner; this review makes no changes to their catalog records.

The accompanying `SELECTION.md` records the read-only semantic review,
remaining wording issues, precise input-domain distinctions, and the IUT
interfaces still needed before any application to the intended comparison.

## Logical dependencies

- `slotwise_commutes_iff`: evaluation of the commutation identity at the
  constant-one tuple; existing `Slots.slotwise_commutes_of_invariant`.
- `deltaTuple_ne_zero`: `zpow_ne_zero` and `ScaleLedger.p_ne_zero`.
- `weightedLedger_relabel_slotwise`: existing `weightedLedger_relabel` and
  `weightedLedger_slotwise`.
- `weightedLedger_combined_invariant_iff`: the combined formula, nonzero delta
  probes, and existing `weightedLedger_delta`.
- `exists_combined_ledger_failure`: the preceding iff, by classical
  contraposition.
- `weightedLedger_relabel_slotwise_support`: existing reindexing formula,
  `vprofile_slotwise` away from zero, and explicit zero-case simplification.
- `weightedLedger_combined_invariant_all_iff`: the nonzero-locus criterion plus
  the support formula and single-coordinate probes.
- `frozen_sigma_marginal_iff`: the definition of the fixed-layer relation and
  `Admissibility.latticeAdmissible_attained`, witnessed by `ScaleLedger.shift`.
- `rectangular_nonempty_unique_layer`: the explicit nonempty witness supplies
  existence; `Admissibility.rectangular_subrelation_freezes_layer` supplies
  uniqueness for any other witnessed marginal.

No theorem assumes its own conclusion. No `sorry`, `admit`, new axiom, opaque
unproved declaration, or admission artifact was introduced.

## Verification

Working directory: `D:\Inter-universal Teichmüller Theory\bridge`.

```powershell
lake env lean --json -DwarningAsError=true IUTBridge\Integration.lean
```

The first run (`lean-integration-01.log`) failed on a missing classical
decidability instance in a theorem statement and a redundant `simpa`. Those
were corrected. The second run (`lean-integration-02.log`) exited `0` with no
diagnostics, checking all seven theorems including the all-tuples criterion.
An empty second log means there were no JSON diagnostic messages.

The audit run appends `#print axioms` for all seven declarations to the exact
source in memory and sends it to:

```powershell
lake env lean --stdin --json -DwarningAsError=true
```

The audit exited `0`. All seven declarations depend only on the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms; no `sorryAx` occurs.
Its outputs are recorded in `axioms.log`. The parent integration must still
perform its normal fresh dependency build, catalog checks, and any separately
required acceptance workflow; this report is a Lean source check, not a UI
receipt or fact-tree admission.

### Final two-wrapper extension

At the parent's explicit request, `Integration.lean` also imports
`IUTBridge.Admissibility` and adds the two frozen-layer wrappers listed above.
The original seven theorem statements and proofs were left unchanged.
The complete nine-theorem file passed the same warning-as-error command with
exit `0` and no diagnostics, recorded in `lean-integration-final.log`.
The final axiom query over all nine declarations is saved in `axioms-final.log`.
It exited `0`; every declaration depends only on `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. The frozen source SHA-256 is
`39DC644B61266D3B79E333A32D25C246A7B28A65DFC5220673AE0A679A9688BC`.
