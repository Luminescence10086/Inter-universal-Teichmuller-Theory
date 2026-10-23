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

## W1：读数不变性（K4 之后的一步）

`h1-decision.md` §结论一′ 定下 `(n,◦)` 是"determined, up to isomorphism"的单对象（原文 8869–8873），
于是留下一条义务：**读数必须与呈现的选择无关**。M3 已证明 11 个接口都不承担这条不变性，所以只能自己证。

`candidates/core-transport/ReadingInvariance.lean`（sha `c9cb9bcd…`，166 行）在 `ℚ_[3]` 上把这条形状做出来：

- `hasSum_perm`：`‖x-1‖<1` 时，按**任意**枚举 `σ` 求和仍得 `localLog x`（引 `Equiv.hasSum_iff`，不重证收敛；
  本机 Mathlib 无 `tsum_perm`）
- `reading_independent_of_enumeration`：两个呈现 `σ,τ` 给出同一 `tsum`，两边都保留为 `tsum`
- `partialSum_not_invariant`：**反退化**——**部分**读数不变性不成立，具体见证 `σ = swap 0 2, n = 1, x = 4`
  给出 `9` 与 `3`，用范数 `‖9‖ = 1/9 ≠ 1/3 = ‖3‖` 分开

三关：CLI `lake env lean -DwarningAsError=true` exit 0、stderr 0 字节（严格门禁 10 声明 / 0 error / 0 warning、
10 定理全有公理报告、公理仅三标准条）；编辑器 0 error / 0 warning / 24 information；Infoview 9/9 `No goals`。

**这是 Ind1–Ind3 的类比，不是它本身**：呈现是"步骤枚举"，不是 Θ-link 的不定性；不构造 Θ-link、`Ism`、
prime-strip、Hodge theater、coricity；不解除 §结论一′ 对真实对象的义务。核心 GAP 仍 OPEN。

## 一个取证工具缺陷（已修，必须留痕）

W1 的第一次编辑器抓取被**拒绝**（exit 3）——新启动的 VS Code 在目录加载完之前标题只有
`Visual Studio Code`，我的守卫按设计拒绝。修这个时又发现更糟的一处：`capture-vscode-2.ps1` 曾在一次
`Get-Content`/`Set-Content` 改写里把中文 UI 模式串**双重编码成乱码**，于是"受限模式"检测可能**假阴性**
（把未信任窗口当成已信任）。

两处都已修：脚本改为等标题出现目录名；所有本地化 UI 模式串改为 `\uXXXX` 转义、文件保持纯 ASCII。
对既有收据的影响：T3 与 K4 的编辑器抓取早于本修复；它们的"已信任"依据**不是**字符串匹配，而是
**Lean 4 状态项与 InfoView 的存在**（受限模式下这两者都不出现），故那些观测仍成立，但旧脚本内的信任检查
不可靠、现已修好。这条注记写下，是为了以后读收据的人不必猜哪个版本产出了哪份证据。

## W2 / W3：两项 Lean 与一项文档（目标三项的收尾）

**W2 — `candidates/core-transport/CollectionProvenance.lean`**（sha `cddea79c…`，526 行）：把 provenance 从单个
元素抬到 **local-global collection**：每个局部件的轨迹由 `steps_eq : steps = algorithmRun input` 按定义钉死，
局部读数由极限唯一性**推出**，全局读数经一个 toy localization 与局部相连。反退化取了**首选形式**——两个同为
`n = 1` 的 collection、局部读数全部落在 `logImage ℚ_[3]`、全局读数不同；执行者还记录了使更强形式在本 toy
中**不可能**的那条（`both_readings_unique`：相同 `localInput` 强制相同读数）。

**W3 — `candidates/core-transport/DivideBackLaw.lean`**（sha `904cbf9b…`，243 行）+ `h3-prerequisites.md`：
玩具层面的"除回 M 次 tensor power"法则（由既有 `padicLog_pow` 导出，不重证），以及同一 `x = 4, M = 2` 处
**范数读数失败**的反例（`1/2` 对 `1`）。文档把 M2 的三条账面发现写成义务，每条带定位，并标注哪条是我自己
回原文核过的（〔已核〕）还是转引 M2 的（〔M2〕）。

三关：两者 CLI `lake env lean -DwarningAsError=true` **exit 0 / stderr 0 字节**（严格门禁 W2 33 声明、W3 16 声明，
全 0 error / 0 warning，公理仅三标准条，无 `sorryAx`）；两者编辑器 **0 error / 0 warning**。Infoview：W3 读到
10/13 零目标，3 处未读（原因是我自己的光标行号助手偏一两行，落在 docstring 上，**不是** Lean 失败，已在
`W3/editor-check.md` 写明）；W2 未做 Infoview（目标要求的三关已满足）。

## 本轮又修掉两处我自己的工具缺陷

1. **检查器把 docstring 当代码**：`theorem is …` 这类正文行被计为声明，导致"未报告公理"的假警报。已在枚举声明
   前先剥注释，并用"植入 `sorry`"的负对照复校准（仍 FAIL）。
2. **Infoview 光标行号助手**：原先把 `/-! … -/` 段注释算进上一块的块体，使光标越过声明落到注释上；已改为
   "任何注释区都不算块体"。改后仍有 3 处偏一两行，如实留作未读项。

另有一处**执行者纠正了我**：我在任务书里写 `‖16‖ = ‖3‖²`-style，但 `16 = 2⁴` 是单位，`‖16‖ = 1`（不是 `1/9`）；
分离仍成立（`1/2 ≠ 1`）。这条错误按原样记下，不修饰。

## W4 与 IUT II 取证（本轮）

**IUT II 已取到并入库**：`research/round2-source-cache/iut-II-official-retrieved-2026-10-23.{pdf,txt}`。
PDF sha256 `180bfa6a…39b7c`（1,203,855 B，标题页 "December 2020"，174 页）；文本化用 `pypdf 6.21.2`
（`extract_iut2.py`），txt sha256 `7d5b7bd7…e7fab`，分页标记与 I/III/IV 一致。缓存里另有一份下载清单 JSON
（非本轮所写），我按其 url/sha/bytes 与实物逐项核对后采用。

**对齐义务的依据找到了**：IUT II **Corollary 4.10(i)**（txt 7003–7010）原文把
`Ψcns(†F≻)_0` 与 `Ψcns(†F≻)_{⟨F_l^⋆⟩}` **认同**，并由此定义 `†F⊩_△`——正是 IUT III 10922–10924
所指的那处。于是 H3 第一条义务由"补一个缺失的约定"降级为"引用该认同，把 (xi-d) 的 `|F_l|` 索引对齐到
procession 归一化"。文档严格区分了**已确立**（认同存在）与**仍属推断**（(xi-d) 未明写它用这个约定）。

**W4 — `candidates/core-transport/TransitionCompatibility.lean`**（sha `391bee2f…`，637 行）：把 W2 的
toy 等式换成**带余圈律的过渡**；相容链迫使读数相同，断裂链（基本过渡相同、直接过渡 `16` vs `64`）分离读数。
CLI exit 0、50 条公理报告、0 诊断；编辑器 0 error / 0 warning。

**又修了两处我自己的缺陷**：检查器对带命名空间的声明与短名比对不一致（已两侧统一按末段比较）；W4 有 4 个定理
缺公理报告（审计遗漏，非证明缺陷，我补了 4 行 `#print` 未改证明）。两处修完都用植入 `sorry` 的负对照复校准。

## W5 / W6：对齐的代数内容与"下降到商"

**W5 — `candidates/core-transport/NormalizationAlignment.lean`**（sha `03b6e502…`，406 行，31/31 审计）：
把 `0 ↔ ⟨F_l^⋆⟩` 认同（IUT II Cor 4.10(i)）的**代数内容**证成定理——不变读数在轨道上取值相同，故
**轨道平均 = 标签处取值**（`average_eq_value_of_invariant` 与其特例 `alignment`）。反退化是**算出来的**：
标签交换下读数 5、7，轨道平均 6，标签处 5，且显式证明不变性假设确实失效；文件还主动披露自作用载体上
不变性即常值性。

**W6 — `candidates/core-transport/ReadingFactorization.lean`**（sha `6a756a88…`，881 行，83/83 审计）：
把 W4 的"链上常数"推进为"**下降到商**"——`SameObject` 取 transport 关系的 `ReflTransGen` 闭包（相容链上多余，
一般情形必需），`descendedReading` 用 `Quotient.lift` 构造、常数性义务逐步证明，`descendedReading_mk`
说明下降函数算出原读数。断裂链上基本单位仍然 transport、直接单位不 transport，读数因此不同，
于是**根本不存在通过商的因子化**（`no_factorization_on_broken`）——这正是轨道形状的失败。

两者：CLI exit 0、stderr 0 字节、0 诊断、每条声明都有公理报告、公理仅三条标准；编辑器 0 error / 0 warning。
均**不**声称 IUT 的 localization 数据、log-volume 或 Θ-link 的任何事；W5 明确不证明 (xi-d) 用的是 procession
平均——来源对齐仍是**定义对齐**。

## 下一步（不属本批次的机械任务）

1. 按 M1 的端点在原文层面定下"环境范畴"与商类型，再决定 W2/W3 的层（H1）。
2. 补 K4：一个真的"合法执行"实现，而不是落点条件（`realisation` 只能当落点用）。
3. 在 (Ob4)/(Ob4-3) 处补"除回 M 次 tensor power"的定量或不变性陈述，并钉死 M 的唯一性（H3 前置）。
4. 对齐 `j∈|F_l|` 归一化与 Prop 3.9(iii) 全局归一化，否则 `vQ = q₀` 无明确含义。

## R1–R4 复查修正（2026-10-23，对照 fix-handoff）

外部复查给出四条意见，逐条处理，记录见 `handoffs/core-backward-2026-10-23/fix-delivery.json`。

1. **R1（结论错误，已撤回）**：此前把 W5/W7 的"沿轨道不变 ⇒ 下降到商"当成 (9-1) 的**必要条件**。
   这是错的：存在使两张映射相等的选择，**不蕴含**读数对整个族不变；反例即在
   `research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean` 的
   `existence_does_not_force_invariance`。本报告与 `PATH.md` 相应两处已改写，W5/W7 现在被表述为
   **另一条更强的族条件**，不是 (9-1) 的前提。
2. **R2（成立，改源件）**：W9、W10 曾用 `set_option linter.unusedVariables false in` 压掉未用变量告警。
   现已删除该开关并**删去多余假设**：W9 的 `hMN` 去掉、新增 `torsion_probe_witness` 把 0 与 1 两个指数
   写出；W10 的 `comparison_well_defined` 不再携带未用的探针假设，探针条件只留在真正用到它的
   `exponent_unique`。两份源件重新过 CLI 与严格检查，`check.json` 已刷新。
3. **R3（成立，证据不足，标签下调）**：W11 的编辑器关曾以"空的 Problems 面板"为据。四次抓取
   （工具记法、退出码与逐条判定见 `handoffs/core-backward-2026-10-23/W11/editor/README.md`）中，
   面板确实被过滤到该文件、**该文件零行**，但同一面板另有 47 条属于其它文件的信息行——说明该通道会发布
   这类行，而本文件在这几次会话里**没有被精化**。因此"零行"不构成"零诊断"的读数，W11 的编辑器关
   下调为 `CLI_CHECKED_EDITOR_PENDING`，公理足迹仍由 CLI 侧承担（43 条报告）。同样的读数还发现
   **W8、W9 的证据树里一条公理行都没有**，两者一并下调；其余任务证据树中的公理行属于**同窗口的其它文件**
   （例如 W10 的树里是 `ExponentUniqueness` 的行，不是 `H3Synthesis` 的），这一口径已写入
   `fix-delivery.json` 的 `editor_evidence_sweep`，是否整体重标由复查方决定。
4. **R4（成立，文档已改）**：页码标记按检索文本重数（54 → **50**）；"同一对象两种呈现"改为
   "**同一兼容性目标的模型化接口，忠实性尚未证明**"；仓库比对补齐 **6 个新增 Lean 文件**与
   **5 个修改的既有 Lean 文件**，不再只说"若干新增"。

三关结论不变：核心 GAP 仍 **OPEN**；本批次没有任何结论被提升为 IUT 的定理。

