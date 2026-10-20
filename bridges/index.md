# Bridge contracts

生成时间：2026-10-20T07:46:41.942874+00:00；状态：`all_contracts_checked`。

三套工程、两套工具链。`local → bridge` 是**真实 Lean import**（内核检查）；
`main → bridge` **无法 import**（Lean 4.34.0 vs rc2），因此那里的边是**受审计的接口合同**：
比较规范化后的 elaborated statement 文本与 vendored 定义的类型，**不是**证明转移。

| 合同 | 类型 | 抽象端 | 具体端 | 结论 |
|---|---|---|---|---|
| `BR-01` | instantiation | `IUTAudit.Scale.scale_composition` | `IUTBridge.ScaleLedger.norm_factor_pow`<br>`IUTBridge.ScaleLedger.valuation_ledger_composition`<br>`IUTBridge.ScaleLedger.composeShift_eq_shift_sum` | checked |
| `BR-02` | instantiation | `IUTAudit.Scale.normalization_at_unit` | `IUTBridge.ScaleLedger.map_one_determines`<br>`IUTBridge.ScaleLedger.existsUnique_layer_of_auto` | checked |
| `BR-03` | statement_identity | `IUTAudit.Transport.rectangular_iff_product` | `IUTBridge.Admissibility.rectangular_iff_product` | checked |
| `BR-04` | instantiation | `IUTAudit.Transport.coupled_choice_counterexample` | `IUTBridge.Admissibility.not_rectangular_of_graph`<br>`IUTBridge.Admissibility.marginals_do_not_force_joint`<br>`IUTBridge.Admissibility.normalised_isRectangular`<br>`IUTBridge.Admissibility.normalised_sigma_marginal` | checked |
| `BR-05` | new_result | `—（新结果）` | `IUTBridge.ScaleLedger.cost_exact`<br>`IUTBridge.ScaleLedger.layer_image_shift`<br>`IUTBridge.ScaleLedger.layer_ssubset_of_lt` | checked |
| `BR-06` | new_result | `—（新结果）` | `IUTBridge.Admissibility.rectangular_subrelation_freezes_layer`<br>`IUTBridge.Admissibility.normalised_isRectangular` | checked |
| `BR-07` | instantiation | `IUTAudit.LocalNumerics.swap23_tuple_and_theta` | `IUTBridge.Slots.relabel_slotwise`<br>`IUTBridge.Slots.valuation_relabel_slotwise`<br>`IUTBridge.Slots.slotwise_commutes_of_invariant`<br>`IUTBridge.Slots.slotwise_not_commutes_of_witness`<br>`IUTBridge.Slots.swap23_exchanges_high_slots` | checked |

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

The rectangularity interface (LeftAllowed, RightAllowed, IsRectangular) and the equivalence 'rectangular iff the joint relation is the product of its marginals' are the same proposition in both toolchains.

- ✅ abstract endpoint elaborated: IUTAudit.Transport.rectangular_iff_product
- ✅ 1 concrete endpoint(s) elaborated, axioms approved
- ✅ elaborated statements identical after prefix normalisation
- ✅ vendored definition type identical: LeftAllowed
- ✅ vendored definition type identical: RightAllowed
- ✅ vendored definition type identical: IsRectangular
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

In the base field, moving the ladder container from one layer to another costs exactly the exponent difference and nothing else, and the ladder is a strictly increasing infinite filtration. This supplies the exact price of a container-widening repair at the level of base-field lattices, without any claim about IUT volumes.

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

