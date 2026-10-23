# 倒推批次收尾（2026-10-23）

本批次按 `handoffs/core-backward-plan-2026-10-23.md` 执行：M1–M4 交机械化静态准备，H1–H3 归主线。四项全部交付，
状态如下。**核心 GAP 仍 OPEN**；本批次没有新增 Lean 证明、没有运行 Lean、没有操作编辑器、未入 fact-tree。

| 任务 | 交付 | 状态 | 主线抽查后的实际结论 |
|---|---|---|---|
| M1 箭头/端点 | `M1/arrows.csv`（28 行）、`sequence.md`、`QUESTIONS.md` | `STATIC_ONLY` | Remark 3.10.2 的图**可从提取文本读出**（p.152）；IPL 六项复合与原文逐字相符；复合是**族索引**、其 domain/codomain 原文未给 → `UNRESOLVED`；16 个节点的环境范畴原文未声明 |
| M2 归一化账本 | `M2/normalizations.csv`（27 行）、`QUESTIONS.md`（10 项） | `STATIC_ONLY`（修复后） | (Ob4) 与 (Ob4-3) 只是**断言**排除了 M 次 tensor power 的混淆，无界、无不变性证明；**M 从未赋值**；`j∈|F_l|` 归一化与 Prop 3.9(iii) 的全局归一化**都未写出** |
| M3 接口保留 | `M3/interfaces.json`（11 项）、`delta.md` | `STATIC_ONLY` | **F3（显式要求合法执行路径）对 11 项全为 false**；F4 只有 `ThetaShift` 的**等式**，所有上界都是独立定理；F1 在 9/11 缺失（`Choice` 瞄 Θ-pilot） |
| M4 可复用构造 | `M4/reuse.csv`（8 条）、`missing.md` | `STATIC_ONLY` | 需要 2（作用＋等变）已覆盖；需要 3 部分；需要 1 部分且被削弱（`ρ_v` 不是字段）；**需要 4 是假设字段**（`pullback_surj` 251），沿 log-link/Θ-link/cQ3/cQ4 一条都没有，商下降空白；需要 5 分离 |

## 主线产出

`research/core-backward-2026-10-23/design-h1-h3.md`：联合见证的最小类型（W1–W6）、构造与下降方案、精确/近似
两条读数路线的量词、以及 M1–M4 回填后的硬约束。三处会改变设计（不是补引用）：

1. **商类型**：原文的 poly-morphism 是集合层 orbit，而 cQ3 的结论对象是 formal/stack-theoretic 商。若模型只
   实现集合层，它弱于 cQ3，`vQ = q₀` 不能顺移。
2. **环境范畴未声明**：上下两排节点索引不同（`(n,m)` vs `(n,◦)`）却画成同一类，K1 在定范畴前无法把 zig-zag
   写成箭头。
3. **K4 的真缺口**：11 个接口没有一个要求"由算法执行产生"，`out` 是裸字段；允许性只能由新证明提供。

## 接收核对与一个工具教训

主线独立复核了：图的文本存在性、IPL 原句、`(Ob4)` 断言原文、`(xi-d)` 的 `j∈|F_l|` 归一化、M4 的六处声明行、
以及三份 CSV 的解析完整性。

**M2 首版 CSV 有 15/27 行错列**（字段内逗号未加引号），而 M2 自报"已用 CSV 解析器回读、无错行"是**假通过**——
它用的是 `Import-Csv`，该命令对多余逗号宽容。已退回修复，M2 用 `TextFieldParser` 与 `csv.reader` 双解析器复核后
通过（27 行 × 11 列、0 错列、0 空字段），主线再独立复解析一次确认。教训：**自检工具比被检对象更宽松时，自检无效**。

## H1 与 K4 的收尾（本批次之后的两项）

**H1 已完成**（`h1-decision.md`）：环境范畴原文声明过（`F⊩▶×μ-prime-strips`，9287–9296、8560/8587）；
商是两层——`⊼fQ₁` 的集合层 orbit（8570–8571）与 `⊼fQ₂ modulo ⊼fQ₁` 的形式商（8607–8629），原文把后者与
"由 log-volume 这类集合不变量给出的 coarse/set-theoretic 商"明确对照。故 W3 的约束是"两层都要、禁止层间偷换"；
log-volume 一出现即已粗化。此前 M1 的发现 #1 与本设计稿的 §1′(a)(b) 都已更正。

**K4 已交付并三关验证**（`handoffs/core-backward-2026-10-23/K4/`）：
`candidates/core-transport/ExecutionProvenance.lean`（sha `f37a80d6…`，208 行）。
`LegalExecution` 用 `steps_eq : steps = algorithmRun input` 把轨迹**按定义**钉在算法上，于是
`value_eq_localLog` 从收敛＋唯一性**推出**值，`value_unique` 说明值只由输入决定，`value_mem_logImage`
是推出而非字段——这正是与 `EtaAlg.realisation` 的对照。非空性有具体见证（输入 `4`）。

- CLI：`lake env lean -DwarningAsError=true` exit 0、stderr 0 字节；严格门禁 11 声明 / 0 error / 0 warning、
  10 定理全有公理报告、公理仅 `{propext, Classical.choice, Quot.sound}`。**注意**：首跑在文件最后一次改动之前，
  已在最终哈希上复跑，记录的是复跑结果。
- 编辑器：0 error / 0 warning / 14 information（其中 10 条是本文件的公理信息）。
- Infoview：9 个证明全部读到 `No goals`/`Goals accomplished!`（`value_mem_logImage` 的空白行位置两次读空，
  改在证明行末读取，判据相同）。

**K4 的诚实边界**：算法是 p 进对数的部分和算法，**不是 η-算法**；没有把任何 IUT 接口改写成带来源的形式；
没有 Θ-link、`Ism`、Cor 3.12。核心 GAP 保持 OPEN。

## 下一步（不属本批次的机械任务）

1. 按 M1 的端点在原文层面定下"环境范畴"与商类型，再决定 W2/W3 的层（H1）。
2. 补 K4：一个真的"合法执行"实现，而不是落点条件（`realisation` 只能当落点用）。
3. 在 (Ob4)/(Ob4-3) 处补"除回 M 次 tensor power"的定量或不变性陈述，并钉死 M 的唯一性（H3 前置）。
4. 对齐 `j∈|F_l|` 归一化与 Prop 3.9(iii) 全局归一化，否则 `vQ = q₀` 无明确含义。
