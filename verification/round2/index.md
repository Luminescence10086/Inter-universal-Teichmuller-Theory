# fact-tree

已准入 32 个定理；待验收 0 个。

只包含通用条件模型与精确整数检查；Corollary 3.12 和 abc 均未证明。

A→B：B 的 type/proof 经项目 helper 常量依赖最近的目录定理 A。外部库不是准入节点。

| 定理 | 源文件 | 目录定理依赖 |
|---|---|---|
| `IUTAudit.Descent.boolean_quantity_does_not_descend` | `IUTAudit/Descent.lean` | IUTAudit.Descent.invariant_of_descends |
| `IUTAudit.Descent.descends_iff_invariant_of_section` | `IUTAudit/Descent.lean` | IUTAudit.Descent.descends_of_section, IUTAudit.Descent.invariant_of_descends |
| `IUTAudit.Descent.descends_of_section` | `IUTAudit/Descent.lean` | 无 |
| `IUTAudit.Descent.invariant_of_descends` | `IUTAudit/Descent.lean` | 无 |
| `IUTAudit.LocalNumerics.aggregate_bound_does_not_imply_componentwise` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.datum_integer_checks` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.layer_preserves_band` | `IUTAudit/LocalNumerics.lean` | IUTAudit.LocalNumerics.layer_preserves_upper |
| `IUTAudit.LocalNumerics.layer_preserves_upper` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.local_integer_checks` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.repaired_cut_and_cost` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.swap23_rho_positions` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.swap23_tuple_and_theta` | `IUTAudit/LocalNumerics.lean` | 无 |
| `IUTAudit.LocalNumerics.transformed_sum_excludes_cut` | `IUTAudit/LocalNumerics.lean` | IUTAudit.LocalNumerics.layer_preserves_upper |
| `IUTAudit.LocalNumerics.transformed_sum_inside_repaired_cut` | `IUTAudit/LocalNumerics.lean` | IUTAudit.LocalNumerics.layer_preserves_band |
| `IUTAudit.Orbit.envelope_closed` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.envelope_covers` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.envelope_idempotent` | `IUTAudit/Orbit.lean` | IUTAudit.Orbit.envelope_closed, IUTAudit.Orbit.envelope_covers, IUTAudit.Orbit.envelope_minimal_closed |
| `IUTAudit.Orbit.envelope_minimal` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.envelope_minimal_closed` | `IUTAudit/Orbit.lean` | IUTAudit.Orbit.envelope_minimal |
| `IUTAudit.Orbit.fixedLabel_envelope_closed` | `IUTAudit/Orbit.lean` | IUTAudit.Orbit.envelope_closed, IUTAudit.Orbit.swapAction_witnesses |
| `IUTAudit.Orbit.fixedLabel_envelope_full` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.fixedLabel_not_closed` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.image_mem_envelope` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Orbit.swapAction_witnesses` | `IUTAudit/Orbit.lean` | 无 |
| `IUTAudit.Scale.erased_comparison_iff` | `IUTAudit/Scale.lean` | 无 |
| `IUTAudit.Scale.erased_comparison_unbounded` | `IUTAudit/Scale.lean` | IUTAudit.Scale.erased_comparison_iff |
| `IUTAudit.Scale.no_uniform_bound` | `IUTAudit/Scale.lean` | 无 |
| `IUTAudit.Scale.normalization_at_unit` | `IUTAudit/Scale.lean` | 无 |
| `IUTAudit.Scale.normalized_scale_preserves` | `IUTAudit/Scale.lean` | IUTAudit.Scale.normalization_at_unit |
| `IUTAudit.Scale.scale_composition` | `IUTAudit/Scale.lean` | 无 |
| `IUTAudit.Scale.scale_two_not_identity` | `IUTAudit/Scale.lean` | 无 |
| `IUTAudit.Scale.weighted_comparison_forces_bound` | `IUTAudit/Scale.lean` | 无 |
