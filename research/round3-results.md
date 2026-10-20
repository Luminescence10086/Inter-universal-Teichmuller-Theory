# 第三轮研究与验证

研究开始于 2026-10-16，恢复与验收日期为 2026-10-19，Asia/Shanghai。**真实 IUT 的争议尚未解决，Corollary 3.12 和 abc 均未证明。** 文献解释仍是研究层；仅明确的 Lean 命题及其验收记录可进入 fact-tree。

## 本轮新增内容

主工程新增 `IUTAudit/Transport.lean` 六个定理：

- `transport_projection`：在显式 dependent fiber cast 下恢复来源分量；
- `transport_comp`：重索引复合与逐次 transport 相同，保留准确的目标 fiber；
- `rho_follows_place`：任意给定 place/rho 函数跟随来源分量；
- `familyImage_bound_iff`：对依赖种子、联合 admissibility 的实际实例逐一给界，等价于约束其像；
- `rectangular_iff_product`：联合允许关系能改成两个边缘投影的笛卡尔积，恰需 rectangularity；
- `coupled_choice_counterexample`：Bool 对角关系的每一边缘选择均允许，特定交叉配对仍被禁止。

这六个是通用接口，不是对真实 IUT 的 κ/σ 允许关系的判定。尤其有限反例并不证明实际 IUT 允许族具有同样耦合；它说明该独立性不能仅凭实现习惯加入。

## 从真实线性代数到层保持的一个子接口

新建独立 `local-field/` 工程，复用本机已存在的固定 Mathlib 与匹配 Lean rc2。其五个定理使用实际 `LinearEquiv`、点乘集合和 ℚ_p：

```text
image_scalar_layer
scalar_layer_membership_iff
threshold_iff_of_layers
padic_threshold_iff
padic_unitBall_layer_membership_iff
```

前两个把“线性等价保持 L”推进到“保持每个 a·L”及其成员资格等价。后两条 p-adic 特化中的最后一条使用真实范数单位球，不需要额外的 layer/measurement 对应假设。

阈值结论仍显式要求集合层与测量阈值的对应；没有把这一目标包装成已证结论。测量仅对非零元素使用，并单独证明线性等价的像也非零。没有把 ord(0) 的 ∞ 偷换成整数 0。L 也未被误设为 ℚ_p 子空间。

因此本轮完成的是线性代数子接口。实际 log-shell 的解析身份、有限扩张的 ramification 条件、真实 Ism 的有限限制以及完整 packet 坐标图仍是开放义务。

## 收紧研究目标

根据 [第三轮语义审计](round3-semantic-audit.md)，IUT II Example 1.8(iv) 已给 Ism 的所有 open-H lattice 条件，Definition 4.9(i) 已给 Kummer orbit 定义。第二轮的表述应收紧为“尚未实现同一个联合数据族的具体坐标和等变性”，不应说原文完全没有轨道定义。

Ind3 中有非可逆 inclusions/surjections。针对 G03 那个具体局部异议，第一目标应是一条实际 seed→κ→σ=(2 3)→输出的联合允许 witness，而非全部 Ind1/2/3 的群作用闭包。八项可执行义务见 [真实接口台账](round3-realization-obligations.md)；它们仍为 open。

本轮还区分了整数幂格层、ceil 估值层与精细 valuation；有限保格条件不能自动赋予每个点的精细 valuation 不变。报告中的二次扩张候选例尚未形式化，不纳入事实树，也不用于宣布真实 Ism 具有该行为。

## 复现与证据

主工程使用 Lean 4.34.0，局部域工程使用 Lean 4.34.0-rc2，分别执行各自的 `tools/verify.py`。本轮新增 11 个定理已完成验收：主工程六项，局部域工程五项。

2026-10-19 最终验证输出：

| 工程 | 准入节点 | 依赖边 | 待验收 | VS Code information | error / warning |
|---|---:|---:|---:|---:|---:|
| 主工程 | 38 | 14 | 0 | 76 | 0 / 0 |
| 局部域工程 | 5 | 4 | 0 | 10 | 0 / 0 |
| 独立图合计 | 43 | 18 | 0 | — | 0 / 0 |

所有证明源文件的 `lean --json -DwarningAsError=true` 检查退出码均为 0，stdout/stderr 均为空。六个新增 Transport 定理不依赖任何公理；所有目录目标的传递公理均在 `propext`、`Classical.choice`、`Quot.sound` 白名单内，无 `sorryAx` 或新增目标公理。每个目录目标在 VS Code 入口逐项 `#check` / `#print axioms`，六份证明源文件的对应终点均实际显示 `No goals`。这些是通用模型和明确前提下的 ℚ_p 接口，不能据节点数量推断 IUT 已得到证明。

验证器延用辅助定义依赖追踪、传递公理检查、源码/导入产物快照及真实 VS Code 观察门禁。观察凭据支持按轮保存并拒绝路径穿越，36 项工程回归测试通过；这些 Python 测试不作为数学节点。

局部域工程的编辑器曾报告 imports 过期：裸 `lean -o` 虽可生成有效编译产物，却没有同步 Lake 追踪记录。已经改为 `lake --no-cache --wfail build LocalFieldAudit`，正常构建成功；随后 VS Code 入口显示 10 条 information、0 error、0 warning，源文件对应的 InfoView 显示 `No goals`。过程日志保留在 `local-field/verification/editor-dependency-build.json`，后续验证使用相同 Lake 构建路径。

本轮的最终数量与验收状态以各工程的 `fact-tree/facts.json` 为准。总入口 `fact-tree/catalogue.md` 和 `registry.json` 由 `tools/forest.py refresh --deep` 生成；查询会校验两份独立源快照，不能据总入口创造跨版本 Lean import 或依赖边。

查询示例（在根目录执行）：

```powershell
python tools/forest.py query rectangular
python tools/forest.py query padic
```

需重算两套导入产物哈希时追加 `--deep`。编辑器观察与绑定凭据分别保存在根目录和 `local-field/` 的 `verification/` 中；来源缓存的 10 项哈希核对见 `verification/round3-source-hashes.json`。

最终工程审计保存为 [round3-final-audit.json](../verification/round3-final-audit.json)：两图均无环、目录依赖完整、编辑器凭据绑定有效、八份源码检查日志为空、10 项来源缓存哈希匹配。`forest.py refresh --deep` 成功，两条查询示例均成功返回对应定理及其前提、公理和依赖。统一目录是两图的不交并，没有跨工具链依赖边。

六项数学 gap 保持开放。下一项最有信息量的工作是实现一个指定 seed 的真实局部坐标与联合允许 lift，再判断原稿中的那条投影路径是否存在。
