# fact-tree

已准入 24 个定理；待验收 0 个。

只包含线性代数及 p-adic 条件接口；Corollary 3.12 和 abc 均未证明。

A→B：B 的 type/proof 经项目 helper 常量依赖最近的目录定理 A。外部库不是准入节点。

| 定理 | 源文件 | 目录定理依赖 |
|---|---|---|
| `LocalFieldAudit.ContinuousLinearity.image_scalar_layer` | `LocalFieldAudit/ContinuousLinearity.lean` | LocalFieldAudit.ContinuousLinearity.map_padic_smul, LocalFieldAudit.Shell.image_scalar_layer |
| `LocalFieldAudit.ContinuousLinearity.map_padic_smul` | `LocalFieldAudit/ContinuousLinearity.lean` | 无 |
| `LocalFieldAudit.ContinuousLinearity.preserves_integerIdealImages` | `LocalFieldAudit/ContinuousLinearity.lean` | LocalFieldAudit.ContinuousLinearity.map_padic_smul, LocalFieldAudit.Filtration.preserves_integerIdealImages, LocalFieldAudit.Filtration.preserves_maximalIdealImage_iff_ball |
| `LocalFieldAudit.ContinuousLinearity.preserves_maximalIdealImage_norm` | `LocalFieldAudit/ContinuousLinearity.lean` | LocalFieldAudit.ContinuousLinearity.map_padic_smul, LocalFieldAudit.Filtration.preserves_maximalIdealImage_norm |
| `LocalFieldAudit.ContinuousLinearity.preserves_maximalIdealImage_valuation` | `LocalFieldAudit/ContinuousLinearity.lean` | LocalFieldAudit.ContinuousLinearity.map_padic_smul, LocalFieldAudit.Filtration.preserves_ball_valuation, LocalFieldAudit.Filtration.preserves_maximalIdealImage_iff_ball |
| `LocalFieldAudit.Filtration.integerIdealImage_eq_pow_ball` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_maximalIdeal_pow_iff_norm_le |
| `LocalFieldAudit.Filtration.mem_maximalIdeal_pow_iff_le_valuation` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_maximalIdeal_pow_iff_norm_le |
| `LocalFieldAudit.Filtration.mem_maximalIdeal_pow_iff_norm_le` | `LocalFieldAudit/Filtration.lean` | 无 |
| `LocalFieldAudit.Filtration.mem_smul_ball_iff_norm_le` | `LocalFieldAudit/Filtration.lean` | 无 |
| `LocalFieldAudit.Filtration.mem_zpow_ball_iff_le_valuation` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_zpow_ball_iff_norm_le |
| `LocalFieldAudit.Filtration.mem_zpow_ball_iff_norm_le` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_smul_ball_iff_norm_le |
| `LocalFieldAudit.Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.integerIdealImage_eq_pow_ball, LocalFieldAudit.Filtration.mem_zpow_ball_iff_le_valuation |
| `LocalFieldAudit.Filtration.p_scaling_strict_ball_contraction` | `LocalFieldAudit/Filtration.lean` | 无 |
| `LocalFieldAudit.Filtration.preserves_ball_norm` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.preserves_ball_valuation |
| `LocalFieldAudit.Filtration.preserves_ball_valuation` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_zpow_ball_iff_le_valuation, LocalFieldAudit.Shell.scalar_layer_membership_iff |
| `LocalFieldAudit.Filtration.preserves_integerIdealImages` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.integerIdealImage_eq_pow_ball, LocalFieldAudit.Shell.image_scalar_layer |
| `LocalFieldAudit.Filtration.preserves_maximalIdealImage_iff_ball` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.integerIdealImage_eq_pow_ball, LocalFieldAudit.Filtration.preserves_integerIdealImages |
| `LocalFieldAudit.Filtration.preserves_maximalIdealImage_norm` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.preserves_ball_norm, LocalFieldAudit.Filtration.preserves_maximalIdealImage_iff_ball |
| `LocalFieldAudit.Filtration.preserves_maximalIdealImage_strict_threshold` | `LocalFieldAudit/Filtration.lean` | LocalFieldAudit.Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation, LocalFieldAudit.Shell.threshold_iff_of_layers |
| `LocalFieldAudit.Shell.image_scalar_layer` | `LocalFieldAudit/Shell.lean` | 无 |
| `LocalFieldAudit.Shell.padic_threshold_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.threshold_iff_of_layers |
| `LocalFieldAudit.Shell.padic_unitBall_layer_membership_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.scalar_layer_membership_iff |
| `LocalFieldAudit.Shell.scalar_layer_membership_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.image_scalar_layer |
| `LocalFieldAudit.Shell.threshold_iff_of_layers` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.scalar_layer_membership_iff |
