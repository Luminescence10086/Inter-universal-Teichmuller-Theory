# integrated bridge fact-tree

已准入 73 个定理；待验收 0 个。

所有节点均经过 source audit、定理依赖 DAG 与显式命题前提核验。

| 定理 | 源文件 | 显式前提 | 目录定理依赖 |
|---|---|---|---|
| `IUTBridge.Admissibility.frozen_isRectangular` | `IUTBridge/Admissibility.lean` | 无 | 无 |
| `IUTBridge.Admissibility.frozen_sigma_marginal` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_attained |
| `IUTBridge.Admissibility.latticeAdmissible_attained` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.ScaleLedger.image_ball_eq_layer, IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.Admissibility.latticeAdmissible_not_rectangular` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_attained, IUTBridge.Admissibility.latticeAdmissible_refl, IUTBridge.Admissibility.latticeAdmissible_unique, IUTBridge.Admissibility.not_rectangular_of_graph |
| `IUTBridge.Admissibility.latticeAdmissible_refl` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.ScaleLedger.image_ball_eq_layer |
| `IUTBridge.Admissibility.latticeAdmissible_unique` | `IUTBridge/Admissibility.lean` | hk, hm | IUTBridge.ScaleLedger.layer_injective |
| `IUTBridge.Admissibility.marginals_do_not_force_joint` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_not_rectangular, IUTBridge.Admissibility.marginals_total |
| `IUTBridge.Admissibility.marginals_insufficient_of_graph` | `IUTBridge/Admissibility.lean` | h1, h2, hleft, hne, hright, hun | IUTBridge.Admissibility.not_rectangular_of_graph |
| `IUTBridge.Admissibility.marginals_total` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_attained, IUTBridge.ScaleLedger.existsUnique_layer_of_auto |
| `IUTBridge.Admissibility.normalised_isRectangular` | `IUTBridge/Admissibility.lean` | 无 | 无 |
| `IUTBridge.Admissibility.normalised_sigma_marginal` | `IUTBridge/Admissibility.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_refl |
| `IUTBridge.Admissibility.not_rectangular_of_graph` | `IUTBridge/Admissibility.lean` | h1, h2, hne, hun | 无 |
| `IUTBridge.Admissibility.rectangular_iff_product` | `IUTBridge/Admissibility.lean` | 无 | 无 |
| `IUTBridge.Admissibility.rectangular_subrelation_freezes_layer` | `IUTBridge/Admissibility.lean` | h1, h2, hrect, hsub | IUTBridge.Admissibility.latticeAdmissible_unique |
| `IUTBridge.Integration.deltaTuple_ne_zero` | `IUTBridge/Integration.lean` | 无 | 无 |
| `IUTBridge.Integration.exists_combined_ledger_failure` | `IUTBridge/Integration.lean` | ha, hfailure | IUTBridge.Integration.weightedLedger_combined_invariant_iff |
| `IUTBridge.Integration.frozen_sigma_marginal_iff` | `IUTBridge/Integration.lean` | 无 | IUTBridge.Admissibility.latticeAdmissible_attained |
| `IUTBridge.Integration.rectangular_nonempty_unique_layer` | `IUTBridge/Integration.lean` | hne, hrect, hsub | IUTBridge.Admissibility.rectangular_subrelation_freezes_layer |
| `IUTBridge.Integration.slotwise_commutes_iff` | `IUTBridge/Integration.lean` | 无 | IUTBridge.Slots.slotwise_commutes_of_invariant |
| `IUTBridge.Integration.weightedLedger_combined_invariant_all_iff` | `IUTBridge/Integration.lean` | ha | IUTBridge.Integration.weightedLedger_combined_invariant_iff, IUTBridge.Integration.weightedLedger_relabel_slotwise_support |
| `IUTBridge.Integration.weightedLedger_combined_invariant_iff` | `IUTBridge/Integration.lean` | ha | IUTBridge.Integration.deltaTuple_ne_zero, IUTBridge.Integration.weightedLedger_relabel_slotwise, IUTBridge.WeightedLedger.weightedLedger_delta |
| `IUTBridge.Integration.weightedLedger_relabel_slotwise` | `IUTBridge/Integration.lean` | ha, hx | IUTBridge.WeightedLedger.weightedLedger_relabel, IUTBridge.WeightedLedger.weightedLedger_slotwise |
| `IUTBridge.Integration.weightedLedger_relabel_slotwise_support` | `IUTBridge/Integration.lean` | ha | IUTBridge.WeightedLedger.vprofile_slotwise, IUTBridge.WeightedLedger.weightedLedger_relabel |
| `IUTBridge.ScaleLedger.composeShift_apply` | `IUTBridge/ScaleLedger.lean` | 无 | 无 |
| `IUTBridge.ScaleLedger.composeShift_eq_shift_sum` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.composeShift_apply, IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.ScaleLedger.cost_exact` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.layer_image_shift |
| `IUTBridge.ScaleLedger.existsUnique_layer_of_auto` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.image_ball_eq_layer, IUTBridge.ScaleLedger.layer_injective |
| `IUTBridge.ScaleLedger.image_ball_eq_layer` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.map_one_determines, IUTBridge.ScaleLedger.mem_layer_iff_norm_le |
| `IUTBridge.ScaleLedger.layer_image_shift` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.mem_layer_iff_le_valuation, IUTBridge.ScaleLedger.shift_apply, IUTBridge.ScaleLedger.zero_mem_layer |
| `IUTBridge.ScaleLedger.layer_injective` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.layer_ssubset_of_lt |
| `IUTBridge.ScaleLedger.layer_ssubset_of_lt` | `IUTBridge/ScaleLedger.lean` | h | IUTBridge.ScaleLedger.layer_subset_of_le, IUTBridge.ScaleLedger.mem_layer_iff_le_valuation |
| `IUTBridge.ScaleLedger.layer_subset_of_le` | `IUTBridge/ScaleLedger.lean` | h | IUTBridge.ScaleLedger.mem_layer_iff_norm_le |
| `IUTBridge.ScaleLedger.map_one_determines` | `IUTBridge/ScaleLedger.lean` | 无 | 无 |
| `IUTBridge.ScaleLedger.mem_layer_iff_le_valuation` | `IUTBridge/ScaleLedger.lean` | hx | 无 |
| `IUTBridge.ScaleLedger.mem_layer_iff_norm_le` | `IUTBridge/ScaleLedger.lean` | 无 | 无 |
| `IUTBridge.ScaleLedger.norm_factor_composition` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.norm_shift |
| `IUTBridge.ScaleLedger.norm_factor_pow` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.norm_shift, IUTBridge.ScaleLedger.shift_comp_apply |
| `IUTBridge.ScaleLedger.norm_shift` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.ScaleLedger.shift_apply` | `IUTBridge/ScaleLedger.lean` | 无 | 无 |
| `IUTBridge.ScaleLedger.shift_comp_apply` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.ScaleLedger.shift_ne_zero` | `IUTBridge/ScaleLedger.lean` | hx | IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.ScaleLedger.valuation_ledger_composition` | `IUTBridge/ScaleLedger.lean` | hx | IUTBridge.ScaleLedger.shift_ne_zero, IUTBridge.ScaleLedger.valuation_shift |
| `IUTBridge.ScaleLedger.valuation_shift` | `IUTBridge/ScaleLedger.lean` | hx | IUTBridge.ScaleLedger.shift_apply |
| `IUTBridge.ScaleLedger.zero_mem_layer` | `IUTBridge/ScaleLedger.lean` | 无 | IUTBridge.ScaleLedger.mem_layer_iff_norm_le |
| `IUTBridge.Slots.mixingEquiv_commutes_swap` | `IUTBridge/Slots.lean` | 无 | IUTBridge.Slots.mixingInv_left, IUTBridge.Slots.mixingInv_right, IUTBridge.Slots.mixingMap_add, IUTBridge.Slots.mixingMap_smul |
| `IUTBridge.Slots.mixingInv_left` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.mixingInv_right` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.mixingMap_add` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.mixingMap_not_slotwise` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.mixingMap_smul` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.relabel_injective` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.relabel_slotwise` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.relabel_trans` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.slotwise_commutes_of_invariant` | `IUTBridge/Slots.lean` | h | 无 |
| `IUTBridge.Slots.slotwise_not_commutes_of_witness` | `IUTBridge/Slots.lean` | h | 无 |
| `IUTBridge.Slots.swap23_exchanges_high_slots` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.swap23_fixes_low_slots` | `IUTBridge/Slots.lean` | 无 | 无 |
| `IUTBridge.Slots.uniform_scale_commutes` | `IUTBridge/Slots.lean` | 无 | IUTBridge.Slots.slotwise_commutes_of_invariant |
| `IUTBridge.Slots.valuation_relabel_slotwise` | `IUTBridge/Slots.lean` | ha, hx | 无 |
| `IUTBridge.WeightedLedger.norm_prod_eq_zpow_totalLedger` | `IUTBridge/WeightedLedger.lean` | hx | 无 |
| `IUTBridge.WeightedLedger.pilotLedger_not_invariant` | `IUTBridge/WeightedLedger.lean` | 无 | IUTBridge.WeightedLedger.pilotWeights_not_invariant, IUTBridge.WeightedLedger.weightedLedger_invariant_iff |
| `IUTBridge.WeightedLedger.pilotWeights_not_invariant` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.sum_perm` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.totalLedger_relabel` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.vprofile_delta` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.vprofile_relabel` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.vprofile_slotwise` | `IUTBridge/WeightedLedger.lean` | ha, hx | 无 |
| `IUTBridge.WeightedLedger.weightedLedger_delta` | `IUTBridge/WeightedLedger.lean` | 无 | IUTBridge.WeightedLedger.vprofile_delta |
| `IUTBridge.WeightedLedger.weightedLedger_invariant_iff` | `IUTBridge/WeightedLedger.lean` | 无 | IUTBridge.WeightedLedger.vprofile_delta, IUTBridge.WeightedLedger.weightedLedger_delta, IUTBridge.WeightedLedger.weightedLedger_relabel |
| `IUTBridge.WeightedLedger.weightedLedger_invariant_of_symm` | `IUTBridge/WeightedLedger.lean` | hw | IUTBridge.WeightedLedger.weightedLedger_invariant_iff |
| `IUTBridge.WeightedLedger.weightedLedger_relabel` | `IUTBridge/WeightedLedger.lean` | 无 | 无 |
| `IUTBridge.WeightedLedger.weightedLedger_slotwise` | `IUTBridge/WeightedLedger.lean` | ha, hx | IUTBridge.WeightedLedger.vprofile_slotwise |
| `IUTBridge.WeightedLedger.weightedLedger_uniform` | `IUTBridge/WeightedLedger.lean` | hx | IUTBridge.WeightedLedger.weightedLedger_slotwise |
