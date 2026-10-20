# fact-tree

已准入 5 个定理；待验收 0 个。

只包含线性代数及 p-adic 条件接口；Corollary 3.12 和 abc 均未证明。

A→B：B 的 type/proof 经项目 helper 常量依赖最近的目录定理 A。外部库不是准入节点。

| 定理 | 源文件 | 目录定理依赖 |
|---|---|---|
| `LocalFieldAudit.Shell.image_scalar_layer` | `LocalFieldAudit/Shell.lean` | 无 |
| `LocalFieldAudit.Shell.padic_threshold_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.threshold_iff_of_layers |
| `LocalFieldAudit.Shell.padic_unitBall_layer_membership_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.scalar_layer_membership_iff |
| `LocalFieldAudit.Shell.scalar_layer_membership_iff` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.image_scalar_layer |
| `LocalFieldAudit.Shell.threshold_iff_of_layers` | `LocalFieldAudit/Shell.lean` | LocalFieldAudit.Shell.scalar_layer_membership_iff |
