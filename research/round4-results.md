# 第四轮：实际 ℤ_p 理想过滤与严格阈值

日期：2026-10-19，Asia/Shanghai。**本轮研究不关闭真实 IUT 的六项 gap 或八项 realization 义务；Corollary 3.12 与 abc 均未证明。** 本轮新增 14 个定理已完成 CLI 与实际 VS Code 零错误、零告警验收。

## 研究切口

第三轮的 Shell 模块已证明线性等价保集合则保标量层，但其阈值结论把 layer/measurement 对应作为显式前提。本轮使用 Mathlib 实际的 `ℚ_[p]`、`ℤ_[p]`、`IsLocalRing.maximalIdeal`、范数与 `Padic.valuation`，在基域情形构造这一对应的证明。

`LocalFieldAudit/Filtration.lean` 没有输入名为 log-shell 的任意集合，也没有把所需估值公式放进结构字段。单位球是实际范数球，整数理想像由实际最大理想的自然数次幂经标准嵌入构成。线性映射保持所选集合的相等条件仍是准确、可见的假设。

## 源码声明索引

以下 14 项声明均在 `LocalFieldAudit.Filtration` 命名空间，现已正式准入。源码首次检查与最终验收分开记录；失败尝试不作为事实节点。

| 声明 | 精确作用 |
|---|---|
| `mem_smul_ball_iff_norm_le` | 非零标量 a 的单位球缩放对应范数 ≤‖a‖；允许 x=0 |
| `mem_zpow_ball_iff_norm_le` | 对全部 n:ℤ 识别 p^n 单位球缩放与范数界 |
| `mem_zpow_ball_iff_le_valuation` | 非零 x 的闭层对应 n≤valuation(x) |
| `mem_maximalIdeal_pow_iff_norm_le` | 真正 ℤ_p 最大理想的自然数幂对应范数界；允许 x=0 |
| `mem_maximalIdeal_pow_iff_le_valuation` | 非零 ℤ_p 元素的实际理想/估值对应 |
| `integerIdealImage_eq_pow_ball` | 构造嵌入后的实际理想幂与 p^n 球层之间的双向见证 |
| `mem_zpow_maximalIdealImage_iff_lt_valuation` | 实际最大理想像的全部整数缩放层对应严格界 n<valuation(x) |
| `preserves_integerIdealImages` | 调用第三轮线性集合层定理，得到实际理想像保持 |
| `preserves_maximalIdealImage_iff_ball` | 在 ℚ_p 中，保实际最大理想像与保单位球等价 |
| `preserves_ball_valuation` | 保单位球的 ℚ_p 线性等价保持非零元素的实际估值 |
| `preserves_ball_norm` | 同一映射保持所有元素的范数，零点单独处理 |
| `preserves_maximalIdealImage_norm` | 从实际最大理想像保持直接推出范数保持 |
| `preserves_maximalIdealImage_strict_threshold` | 用已证实际对应实例化第三轮严格阈值接口，没有额外测量对应假设 |
| `p_scaling_strict_ball_contraction` | 构造实际 ℚ_p 线性等价，球像严格包含于球且 1 的范数改变 |

“实际”指这些对象采用 Mathlib 的具体 p-adic 实现，不表示已经实现 IUT 的局部算术数据、Ism、κ 或 Θ-pilot。

## 两个需保留的区别

闭单位球与最大理想使用不同的层编号。新源码分别给出非严格和严格估值界，后者显式经过一阶位移；不把二者混用。涉及 `Padic.valuation` 的层判别均保留非零前提。Mathlib 的有限值 `valuation 0=0` 没有被当作数学扩展估值的 +∞；范数和理想结论则包含零。

另一方面，“全空间上的线性同构”和“某个格的自同构”有不同要求。乘以 p 是实际 ℚ_p 线性同构，但不能满足格像等于原格的条件。形式化反例仅检验把相等弱化为单向包含是否足够，不把它认定为真实 Ism 元素，也不据此反驳原 IUT。

## 一手来源与适用边界

固定 Mathlib commit 为 `85e3a25e006c35636f0e53b0e9296caca2685bc0`，Lean 为 `4.34.0-rc2`。实际阅读与缓存的六份源码列于 `round4-source-cache/manifest.json`，覆盖 p-adic 数、整数、线性等价、集合缩放、理想 span 与集合 image。基础接口可在线定位于 [Mathlib 官方文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicIntegers.html)，但构建以固定本地源码和编译产物为准，滚动网页不能替代该版本。

重新核对 [IUT IV Proposition 1.2](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf)，实际阅读印刷 pp.9–11。原文对 log-lattice 使用诱导自同构的条件；小分歧下的 logarithm-image 控制仍需要解析理论。本轮没有形式化该命题或其 log/exp 理论。本地复用的 April 2020 PDF 字节已与第二轮哈希匹配；本轮网页读取确认 87 页，不声称比对了远端 PDF 字节。

新结论只覆盖基域 ℚ_p。迁移到原文归一化为 ord(p)=1 的分歧扩张前，还须实现其实际值群、归一化与过滤对应；本轮没有证明其 log-lattice、单位群像、有限 Ism 限制或 κ/σ 联合允许性。不能用基域的精细估值结论替代这些桥梁。

对固定本机 `NumberTheory/Padics` 与 `Analysis/SpecialFunctions` 的定向检索没有找到可直接调用的目标 p-adic logarithm-image 接口。这不是 Mathlib 全库不存在该定理的证明，也没有把实或复对数误当成 p-adic 对数。解析身份继续记在 G03 / RI-06。

## 验证与恢复

第三轮根目录与局部域目录的证据、工具及事实图已分别归档至各自 `verification/round3/`。主工程没有新增或修改 Lean 命题，其 38 个节点沿用第三轮实际 VS Code 观察，并于本轮重新完成源码与运行产物深查，见 `verification/round4-core-retained.json`。

局部域工程包含原有五项及本轮十四项，编辑器入口实际显示 38 条 information、0 error、0 warning；Filtration.lean:215:37 和 Shell.lean:95:22 的对应 InfoView 均实际显示 `No goals` 与 `Goals accomplished!`。最终检查导出传递公理及经过辅助定义的目录依赖，重新计算输入与导入产物哈希，结果为 `Admitted=19, pending=0, edges=21`。

| 工程 | 准入节点 | 依赖边 | 待验收 | 观察依据 |
|---|---:|---:|---:|---|
| 主工程 Lean 4.34.0 | 38 | 14 | 0 | 第三轮实际 VS Code 观察，本轮深查确认源码/运行产物未变 |
| 局部域 Lean 4.34.0-rc2 | 19 | 21 | 0 | 第四轮 CLI 与实际 VS Code 观察 |
| 两独立图合计 | 57 | 35 | 0 | 不构造跨工具链证明边 |

局部域的三份源码检查（含主 import）退出码均为 0，stdout/stderr 均为空。全部目标的传递公理均在 `propext`、`Classical.choice`、`Quot.sound` 白名单内，无 `sorryAx` 或自定义目标公理。该准入依赖已安装的 Lean 内核、固定依赖和实际观察记录，不是防伪证书。

实际编辑器观察与绑定凭据位于 `local-field/verification/vscode-observation-round4.txt` 和 `vscode-receipt.json`。来源缓存的八项哈希匹配记录为 `verification/round4-source-hashes.json`；最终工程审计为 `verification/round4-final-audit.json`。

统一调用入口是 `fact-tree/catalogue.md`。在根目录执行：

```powershell
python tools/forest.py query strict_threshold
python tools/forest.py query contraction
python tools/forest.py refresh --deep
```

前两条查询展示准确声明、公理与最近目录依赖；追加 `--deep` 可重新核对两套运行产物。图中的 Shell→Filtration 依赖来自实际 Lean proof 常量，不把尚未实现的 IUT 义务混入正式图。

类型推断事件与修复记录见根目录 `GAP-round4-elaboration.md`。它已经解决；没有把失败编译当成数学反例。未获得真实 IUT 实现的部分仍按 `GAP.md` 记录，不能以这次工程修复代替数学补救。

下一条真实数学目标仍是同一实际 seed、κ 与 σ=(2 3) 的联合见证。新增基域过滤可作为局部工具，尚未提供该见证。
