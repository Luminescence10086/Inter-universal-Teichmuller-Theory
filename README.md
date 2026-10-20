# IUT 形式化研究与争议审计

本项目以补强 IUT 为研究目标，以 Lean 检查和可追溯证据为准入标准。**IUT 的争议尚未解决，abc 尚未证明。** 文献、研究提案、模型定理、真实 IUT 定理必须严格分开。

## 从这里开始

- [争议清单与历史](research/controversies.md)：C01–C06，含两方回应、2026 η 相容性目标及最新 Step (v) 局部异议。
- [来源登记](research/sources.json)：作者、版本、URL、实际阅读范围与未审读项。
- [核心工具链与交叉候选](research/core-and-bridges.md)：I–IV 接口及九个可检验方向；全部是待证明的研究设计。
- [第二轮结果与复现](research/round2-results.md)：轨道模型、局部整数检验、验证器修复及剩余义务。
- [第二轮逐桥梁来源审计](research/round2-source-audit.md)：M1–M5、T1–T5 及四条候选补救路线。
- [第三轮结果](research/round3-results.md)、[真实接口台账](research/round3-realization-obligations.md)：联合选择、实际 ℚ_p 层接口及八项尚未实现的语义义务。
- [第四轮结果](research/round4-results.md)：实际 ℤ_p 最大理想过滤、严格估值层、范数保持与单向包含的反例。
- [第五轮结果与验收状态](research/round5-results.md)：连续加法作用的 ℚ_p 线性、实际过滤推论及联合见证候选；[模型分工](research/round5-delegation.md)。
- [探索成果整合与形式化](research/round8-integration.md)：筛选层梯、联合关系、槽位与加权账本；新增九条组合接口，bridge 完成 73 条声明的 CLI 与实际 VS Code 验收。
- [三工程、两工具链总入口](fact-tree/catalogue.md)：135 个节点、115 条边；跨版本只记录合同，同版本实际 import 单独标记。
- [开放 gap](GAP.md)：六项开放义务及恢复目标；有 gap 就不宣称解决。
- [fact-tree](fact-tree/index.md)：只收已通过本机 Lean 与 VS Code 验收的项目定理。

## 本轮形式化的精确范围

第一轮 12 项、第二轮 20 项；第三轮主工程的 `IUTAudit/Transport.lean` 新增六项显式重索引与联合 admissibility 接口。主目录合计 38 项。独立 `local-field/LocalFieldAudit/Shell.lean` 另有五项 Mathlib 线性等价与实际 ℚ_p 条件接口。第三轮验收时两套工程均完成 CLI 与 VS Code 零错误、零告警检查，合计 43 个准入节点、18 条边、0 个待验收目标；这是第三轮历史状态。

第四轮 `local-field/LocalFieldAudit/Filtration.lean` 新增 14 项实际基域理想/范数/估值接口，完成 CLI 与 VS Code 零错误、零告警验收；当时局部域工程为 19 个节点、21 条边，两工程合计 57 个节点、35 条边。

第五轮 `local-field/LocalFieldAudit/ContinuousLinearity.lean` 新增五条定理：在准确拓扑假设下，证明连续加法作用的 ℚ_p 线性，并导出显式保集合条件下的层、理想幂像、非零估值及范数保持。五条均通过 CLI 与实际 VS Code 零错误、零告警验收；局部域工程为 24 个节点、31 条边。主工程保留 38 个节点、14 条边；第五轮当时合计 **62 个准入节点、45 条边**。

探索整合轮保留上述两树并完成 `bridge/` 的 73 个节点、67 条内部边，新增 3 条 `local-field → bridge` 实际导入边。当前总入口为 **135 个准入节点、115 条边、0 个待验收目标**。bridge 的五份证明源文件及 146 条信息入口均通过实际 VS Code 零错误、零告警观察；schema-3 收据绑定完整输入、依赖与运行产物。真实 IUT 的 log-shell、Ism/Kummer 实现、六项数学 gap 和八项接口义务继续开放。

它们没有定义真实 Hodge theater、Θ-link、anabelian 重建或 Arakelov 体积，因而既不是 IUT 的证明，也不是 IUT 的反证。特别是 `weighted_comparison_forces_bound` 中的前提只是假设的整数不等式；将它连接到真实 IUT 恰是 G01/G02 的工作。

## 复现与调用

在本目录执行（需要已安装的 Lean 4.34.0、Lake 和 Python；本项目不依赖 Mathlib）：

```powershell
lake build
python tools/verify.py
python tools/query.py
python tools/query.py erased_comparison
python tools/query.py --deep repaired_cut
python tools/test_verifier.py
python tools/forest.py query rectangular
python tools/forest.py refresh --deep
```

主工程 `verify.py` 对五份证明源文件及主 import 重新执行 `lean --json -DwarningAsError=true`，要求 stdout/stderr 空；读取真实 elaborated 常量的来源模块、类型、依赖与传递公理；仅允许 `propext`、`Classical.choice`、`Quot.sound`。目录由 `tools/catalog.json` 明确指定，并核对实际声明类型与来源模块。构建成功不自动授权准入。

VS Code 中打开并检查主工程五份证明文件，再打开 `tools/EditorCheck.lean`。该入口逐项 `#check` 和 `#print axioms`，脚本核对每个目录项各出现一次；76 条 information 是预期输出，**error/warning 必须均为 0**。主工程实际 UI 观察保存为 `verification/vscode-observation-round3.txt`，第五轮深查确认输入及运行产物未变；`vscode-receipt.json` 绑定观察文本、输入快照、目标目录与导入产物哈希。它仍是观察记录，不是防伪证书，也不替代 Lean 内核。第一、二轮证据分别保留在 `verification/round1/`、`verification/round2/`。

局部域工程使用匹配现有 Mathlib 的 Lean 4.34.0-rc2，第五轮验收入口实际为 48 条 information、0 error、0 warning，三份证明文件均取得匹配 InfoView 的 `No goals`。其工具、快照和事实树均在 `local-field/` 内独立保存，复现方式见该目录 README。该工程没有实现真实 IUT log-shell 或 packet；实际基域理想过滤不等于完整 Ism/Kummer 实现。第三、四轮原始证据与工具保存在两工程各自的 `verification/round3/`、`verification/round4/`。

证明源码集合（含新增文件）、工具链配置、锁文件、主 import、编辑器入口、导出器、验证器或目录变化，都须重新检查。导入环境的 `.olean`、现存 private/server sidecar 以及实际 Lean/Lake 可执行文件也记录哈希，并在源检查及导出前后核对。普通查询快速检查源快照和图结构；`--deep` 额外重算运行产物哈希。未列入快照的操作系统、DLL、扩展二进制仍属于信任环境；前后快照不能排除恶意修改后还原的竞态。

没有有效编辑器记录时，定理只进入 `verification/candidates.json`。验证开始先关闭旧准入；验收不足会沿依赖传播。临时 `.tmp-round2-verifier/` 中的合成 receipt 仅用于复现旧漏洞，绝不可作为生产准入凭据。

## fact-tree 的语义

`fact-tree/facts.json` 是权威机器入口，`graph.dot` 是有向图。A→B 表示从 B 的实际 type/proof 常量引用出发，经项目辅助常量遇到目录定理 A；遇目录定理即停止该支遍历，后续依赖另有边。第二轮已修复旧版穿过 `def` 漏边的问题，并以真实 Lean 最小例回归。所有项目常量见 `verification/project-constants.json`。

图只包含明确目录中的双重验收 theorem；不是整个 Lean/Std 的完整依赖图，也不是 IUT 证明图。标准库是固定版本的依赖环境，未冒称逐一定理经 VS Code 验收。JSON 与 receipt 在同一可写工作区，脚本用于复现与发现意外漂移，不能宣称抵抗有意伪造。

研究提案的预期依赖链位于争议报告，**不混入正式 fact-tree**。未来新增真实 IUT 节点需要通过相同门禁，语义桥接亦须单独证明。
