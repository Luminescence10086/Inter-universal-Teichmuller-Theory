# Bridge contracts

生成时间：2026-10-20T11:43:39.948437+00:00；状态：`all_contracts_checked`。

三套工程、两套工具链。`local → bridge` 是**真实 Lean import**（内核检查）；
`main → bridge` **无法 import**（Lean 4.34.0 vs rc2），因此那里的边是**受审计的接口合同**：
完整检查准入、源/配置/依赖/运行产物，再比较陈述及指定定义体文本；**不是**证明转移。

| 合同 | 类型 | 抽象端 | 具体端 | 结论 |
|---|---|---|---|---|
| `BR-01` | instantiation | `IUTAudit.Scale.scale_composition` | `IUTBridge.ScaleLedger.norm_factor_pow`<br>`IUTBridge.ScaleLedger.valuation_ledger_composition`<br>`IUTBridge.ScaleLedger.composeShift_eq_shift_sum` | checked |
| `BR-02` | instantiation | `IUTAudit.Scale.normalization_at_unit` | `IUTBridge.ScaleLedger.map_one_determines`<br>`IUTBridge.ScaleLedger.existsUnique_layer_of_auto` | checked |
| `BR-03` | statement_identity | `IUTAudit.Transport.rectangular_iff_product` | `IUTBridge.Admissibility.rectangular_iff_product` | checked |
| `BR-04` | instantiation | `IUTAudit.Transport.coupled_choice_counterexample` | `IUTBridge.Admissibility.not_rectangular_of_graph`<br>`IUTBridge.Admissibility.marginals_do_not_force_joint`<br>`IUTBridge.Admissibility.normalised_isRectangular`<br>`IUTBridge.Admissibility.normalised_sigma_marginal` | checked |
| `BR-05` | new_result | `—（新结果）` | `IUTBridge.ScaleLedger.cost_exact`<br>`IUTBridge.ScaleLedger.layer_image_shift`<br>`IUTBridge.ScaleLedger.layer_ssubset_of_lt` | checked |
| `BR-06` | new_result | `—（新结果）` | `IUTBridge.Admissibility.rectangular_subrelation_freezes_layer`<br>`IUTBridge.Admissibility.normalised_isRectangular` | checked |
| `BR-07` | instantiation | `IUTAudit.LocalNumerics.swap23_tuple_and_theta` | `IUTBridge.Slots.relabel_slotwise`<br>`IUTBridge.Slots.valuation_relabel_slotwise`<br>`IUTBridge.Slots.slotwise_commutes_of_invariant`<br>`IUTBridge.Slots.slotwise_not_commutes_of_witness`<br>`IUTBridge.Slots.swap23_exchanges_high_slots` | checked |
| `BR-08` | instantiation | `IUTAudit.Scale.weighted_comparison_forces_bound` | `IUTBridge.WeightedLedger.weightedLedger_slotwise`<br>`IUTBridge.WeightedLedger.weightedLedger_invariant_iff`<br>`IUTBridge.WeightedLedger.pilotLedger_not_invariant`<br>`IUTBridge.WeightedLedger.totalLedger_relabel`<br>`IUTBridge.WeightedLedger.norm_prod_eq_zpow_totalLedger` | checked |
| `BR-09` | new_result | `—（新结果）` | `IUTBridge.Integration.weightedLedger_relabel_slotwise`<br>`IUTBridge.Integration.weightedLedger_combined_invariant_iff`<br>`IUTBridge.Integration.weightedLedger_relabel_slotwise_support`<br>`IUTBridge.Integration.weightedLedger_combined_invariant_all_iff` | checked |
| `BR-10` | new_result | `—（新结果）` | `IUTBridge.Integration.frozen_sigma_marginal_iff`<br>`IUTBridge.Integration.rectangular_nonempty_unique_layer` | checked |

## 每条合同的机器检查项

### BR-01

The abstract discrete scale model composes multiplicatively. On actual Q_p the multiplicative coordinate is the norm scale factor, and the additive coordinate is the valuation; both are proved to have exactly the predicted composition law, and iterated rescaling telescopes to the sum of exponents.

- ✅ abstract endpoint elaborated: IUTAudit.Scale.scale_composition
- ✅ 3 concrete endpoint(s) elaborated, axioms approved
- ✅ instantiation edge: statements differ by design, no identity claimed
- ✅ contract declares no IUT object constructed
- 未构造：Theta-link, Ism element, Arakelov log-volume

### BR-02

The abstract model proves that a scale is determined by its value on the unit. On actual Q_p the corresponding statement is that the value at 1 determines the automorphism, hence determines exactly one lattice layer of the ball image: the joint data is a graph.

- ✅ abstract endpoint elaborated: IUTAudit.Scale.normalization_at_unit
- ✅ 2 concrete endpoint(s) elaborated, axioms approved
- ✅ instantiation edge: statements differ by design, no identity claimed
- ✅ contract declares no IUT object constructed
- 未构造：Ism group, finite H-invariant module, log coordinate

### BR-03

The rectangularity interface (LeftAllowed, RightAllowed, IsRectangular) and the equivalence 'rectangular iff the joint relation is the product of its marginals' are carried over to the second toolchain: the elaborated statements agree after namespace normalisation, the elaborated types of the three vendored definitions agree, and their full diagnostic printed definition bodies is checked for identity by the auditor. This is an interface-identity audit, NOT a kernel-level proof transfer and NOT a claim of semantic equivalence across toolchains.

- ✅ abstract endpoint elaborated: IUTAudit.Transport.rectangular_iff_product
- ✅ 1 concrete endpoint(s) elaborated, axioms approved
- ✅ elaborated statements identical after prefix normalisation
- ✅ vendored definition type identical: LeftAllowed
- ✅ vendored definition body text identical: LeftAllowed
- ✅ vendored definition type identical: RightAllowed
- ✅ vendored definition body text identical: RightAllowed
- ✅ vendored definition type identical: IsRectangular
- ✅ vendored definition body text identical: IsRectangular
- ✅ contract declares no IUT object constructed
- 未构造：Ind1 operation, procession automorphism, Kummer isomorphism

### BR-04

The abstract Boolean counterexample showing that separate kappa- and sigma-admissibility does not entail joint admissibility is realized on actual arithmetic data: automorphisms of Q_p versus integer layers of the unit ball. Both marginals are total and the relation is not rectangular, because the relation is a graph over an infinite ladder. A general graph obstruction is isolated, and the normalised sub-relation is proved rectangular, so the failure is exactly the rescaling freedom.

- ✅ abstract endpoint elaborated: IUTAudit.Transport.coupled_choice_counterexample
- ✅ 4 concrete endpoint(s) elaborated, axioms approved
- ✅ instantiation edge: statements differ by design, no identity claimed
- ✅ contract declares no IUT object constructed
- 未构造：SeedRegion membership, possible-images family, joint (kappa, sigma) lift

### BR-05

In the base field the ladder is strictly *antitone* — a larger index is a smaller ball, so `k ≤ m` gives `layer m ⊆ layer k` and widening goes towards smaller indices. Moving from `layer k` to `layer m` is realised by the single dilation of signed exponent `m - k`. This is an identity between sets of p-adic numbers; it defines no measure, no volume, no log-volume and no optimal price, and must not be read as a quantitative cost formula.

- ✅ 3 concrete endpoint(s) elaborated, axioms approved
- ✅ contract declares no IUT object constructed
- 未构造：holomorphic hull, tensor normalisation, global error budget

### BR-06

Any rectangular repair freezes the lattice layer. If a sub-relation of the joint lattice relation admits independent marginal reasoning (is rectangular), then all of its admissible pairs share one layer: independent marginal reasoning is available only after the rescaling freedom has been given up. This converts the BR-04 obstruction from a counterexample into a design constraint on any repair attempt.

- ✅ 2 concrete endpoint(s) elaborated, axioms approved
- ✅ contract declares no IUT object constructed
- 未构造：joint (kappa, sigma) lift, seed-region membership, hull bound

### BR-07

The integer slot model of the label action is realized on actual p-adic tuples. Relabelling by a permutation conjugates a slotwise scalar family, so a slotwise action is sigma-equivariant exactly when the family is sigma-invariant; it moves components but preserves each component's valuation data. The main project's swap23 model is a generic-type reindexing with no scalar action, so the conjugation statement is new to this toolchain.

- ✅ abstract endpoint elaborated: IUTAudit.LocalNumerics.swap23_tuple_and_theta
- ✅ 5 concrete endpoint(s) elaborated, axioms approved
- ✅ instantiation edge: statements differ by design, no identity claimed
- ✅ contract declares no IUT object constructed
- 未构造：real Hodge theater slot set, procession automorphism, tensor packet

### BR-08

Arbitrary integer-weighted valuation ledgers on actual p-adic tuples have exact slotwise scaling and relabelling formulas. Preservation under all relabelled tuples is equivalent to invariant weights. Separately, on coordinatewise nonzero tuples, the product of element norms equals p raised to the negative UNWEIGHTED total ledger. The hand-chosen vector (1,1,2,1) is a test example only.

- ✅ abstract endpoint elaborated: IUTAudit.Scale.weighted_comparison_forces_bound
- ✅ 5 concrete endpoint(s) elaborated, axioms approved
- ✅ instantiation edge: statements differ by design, no identity claimed
- ✅ contract declares no IUT object constructed
- 未构造：pilot weight realisation from real theta data, holomorphic hull, tensor normalisation, global error budget

### BR-09

For coordinatewise nonzero scalars, scaling followed by relabelling preserves the weighted ledger on every coordinatewise nonzero tuple iff the weights are invariant and the total weighted valuation budget is zero. On all tuples including zeros, each slot budget must vanish separately. The support formula records the difference of domains.

- ✅ 4 concrete endpoint(s) elaborated, axioms approved
- ✅ contract declares no IUT object constructed
- 未构造：actual admissible input region and its probe tuples, real pilot weights, Ism action identification, measure or volume bound

### BR-10

For every fixed integer c the frozen target-layer relation has marginal exactly {c}. A nonempty rectangular subrelation of lattice admissibility realizes exactly one layer; the nonempty witness is explicit.

- ✅ 2 concrete endpoint(s) elaborated, axioms approved
- ✅ contract declares no IUT object constructed
- 未构造：actual IUT joint admissibility relation, seed-region witness, joint Ism/Kummer realization

