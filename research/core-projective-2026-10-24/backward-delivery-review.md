# 倒推路径交付独立审查

日期：2026-10-24。范围：只读审查倒推路径、现有 `EtaAlg` / `Wall` 类型和交付路径；未运行 Lean / 编辑器，未改既有 `PATH.md`、`round-report.md`、handoff 或 registry。

## 版本和取证边界

主 checkout `explore/correspondence` 的 HEAD 为 `8d60456043e30a3da79cc838d03a19b80675dc98`。它有四个原有 tracked dirty 文件，其中包含 `fact-tree/registry.json`、`handoffs/core-support-2026-10-22.md`、`research/core-backward-2026-10-23/PATH.md` 和 `round-report.md`；本审查没有修改它们。新倒推材料在本机已有的 `research/backward-paths` 分支/远端跟踪分支，无需 fetch 或 checkout：

- `a811a6dd4bb5f38bdab541d7d9c06f30a02e8c74`：六条路径初稿；
- `82bbc0a8780b929dcfcdcabaf9f0f7ee22028f69`：第二层四阻塞；
- `2acc5166d20d0e82cdca97072b29d318026be142`：V2–V5 修订及 layer 3–4 原子交付；
- `d3c5599668aa57c5c00244117abd26787fcd559e`：最新提交，仅新增 `research/core-backward-2026-10-23/backward-paths-layer5-2026-10-23.md`（145 行）。

实时远端核对已执行：`& 'C:/Program Files/Git/cmd/git.exe' ls-remote origin refs/heads/research/backward-paths` 返回 `d3c5599668aa57c5c00244117abd26787fcd559e`；与本地 `research/backward-paths` 的 `rev-parse` 完全一致。本轮无需 fetch，未切换分支。

该分支最新提交本身没有改写主 checkout 的 `PATH.md` / `round-report.md`，也没有包含测量命令的完整 stdout/stderr 文件；其中构建实测和 lakefile 检索是 layer5 文档记录的事实。本轮我独立用 Git 只读复核了文档声称的 `origin/candidates/restore-local-only` 绝对路径命中：`core-log`、`core-compactness`、`nonarchimedean-ring` 和 `pilot-shadow` 命中，符合 layer5 表格；没有复跑构建。

## 核心审查结论

倒推分层对“缺哪些输入/义务”的整理总体诚实，且明确写了核心 GAP OPEN。最短的**可验收条件性路线**确实是 P6：把 (9-1) 显式做成假设，再使用 `EtaAlg` 已有的条件推论。但 P6 不构成从输入证明核心目标的路线。若目标保持为 G0 `q₀ ≤ B` 且不把 (9-1) 偷作输入，当前材料没有一条已经闭合的路线；真正最短的数学链是“真实允许 witness + 它的目标读数等于 q-pilot 读数 + 对同一 witness 的独立上界”，其中中间等式/存在性仍是 (9-1) 核心缺口，真实 witness 与上界的类型连接也未构造。

### P1 — 高：把 P6 的“零前置”误读成通往 G0 的零前置进展

初稿明确定义 P6 为把 (9-1) 当 `ASSUMED_INPUT`，并在边界说结论相对假设成立（`backward-paths-2026-10-23.md:165-180, 211-215`）。layer2 也说 P6 不消费上游叶子、O8/O9 仍开放（`backward-paths-layer2-2026-10-23.md:110-120`）。layer5 将其排为“唯一不依赖任何修复”“可以立刻开工、产出可交付中间态”（`backward-paths-layer5-2026-10-23.md:105-106, 122-124`），这在**代码交付**意义上成立，但不能算 G0 的数学前进。`Iut/Wall/EtaAlg.lean:169-177` 将 `Wall` 定义为对所有 theater / Θ-link 存在 `ι,S` 使 `etaAnab ι S = etaQ` 的 `Prop`；`variant_of_wall` 以 `hW : Wall D A` 为显式参数（`:190-200`）。因此 P6 只能机械验收条件结论，若路线榜把它计为已达到 G0，会把目标结论作为输入。建议把排名名称限定为“最快条件性接口交付”，与所有无该假设的 G0 路线分列。

### P1 — 高：`EtaAlg.realisation` 不是执行来源，也不足以定义原始允许输出

`EtaAlg.out` 是 `BPS.Iso … → Ind3 D → Region D` 的任意结构字段（`Iut/Wall/EtaAlg.lean:105-109`）；`realisation` 仅给 `IsAdelic D (out ι S) ∧ InHullOfImage D (out ι S)`（`:120-125`），没有算法轨迹、合法步骤关系或从原文操作抽取该函数的构造。接口文档也明说“asking only for the hull is weaker”且 `EtaAlg` 因此允许更多算法（`:46-54`）。`ind12_acts_on_S` 只给一个选择置换 `τ` 使输出相等（`:110-114`），并未给实际执行/同源选择的来源。`handoffs/core-backward-plan-2026-10-23.md:41-45, 52-56` 把 K1/K4 和 H2/H3 正确留作待证；本地 `GAP-core-native-realization.md:5-7, 13-23` 也记有 hull 与原文允许操作/actual Hodge 来源的差距。故任何由模型 `EtaAlg` 证明的条件定理，只有在另证真实算法可实例化该结构、且满足所需允许族时才可回到原论证。机械验收可核字段签名和公理；该实例化是数学/来源突破。

### P1 — 高：结果的类型通路是精确的，但其关键 scalar equality 就是目标，不是新输入事实

接口把 `etaAnab` 定义为将 pilot 送到 `logVol (out ι S)` 的线性映射（`:142-147`），并证明
`etaAnab ι S = etaQ D ↔ logVol D (out ι S) = qPilot.lhs`（`:151-153`）。`exists_out_of_wall` 将 witness、realisation 和这个等式组合起来，`variant_of_wall` 再用 hull 上界导出变体（`:185-200`）。这条类型路径没有把映射相等偷换成别的类型：而是明确把它化约为单个输出体积等式。可是这也精确显示 P6 输入已蕴含核心读数条件；不能把 `etaAnab_eq_etaQ_iff` 的等价或其下游当成证明该等式。更关键的是，`variant_of_wall` 用的是 `Corollary312Variant`（该 interface 注释自述为 IUT IV reading），若最终 G0 要严格采用 `q₀ ≤ B` 的原始陈述，还须核对 `qPilot.lhs`、右侧上界及变体/字面版本是否正是同一归一化和目标；已有 `PATH.md:49-69, 80-91` 与 `round-report.md:13-22` 坚持这个边界。

### P2 — 中：P2 的量词规格必要，但还没有共同输出族或一致上界

P2 要对每个 `ε>0` 找真实允许 `Jε`，满足读数 `≥q₀−ε`，并有独立同一个 `B`；文件已明确提醒 `B` 必须落在同一序列上（`backward-paths-2026-10-23.md:86-104`）。这避免了“超集下界”量词错误，规格本身合理。但 layer34 的交付物 D1/D2/D4 并不构造 `Jε`：它们是 log 桥、实侧定义桥和权重签名检查（`backward-paths-layer34-2026-10-23.md:27-68, 109-115`）；layer5 的 E2/E4 同样仍为设计单元（`:57-75`）。故它们是部分前置诊断/机械工程，不能据此声称 P2 具备所需近似族。构造允许族和 uniform `B` 属于数学突破。

### P2 — 中：层 5 的“测量”适合揭穿空构建，但交付中需保留缓存/干净克隆区别

layer5 记录无目标 `lake build` exit 0 实为 `Nothing to build`，显式 `lake build CoreTransport` 才跑 2672 jobs，但明确命中本机 `.lake` 缓存（`backward-paths-layer5-2026-10-23.md:10-19`）。同时它发现 lakefile 固定本机 Mathlib 路径（`:21-41`）。这可靠支持“不能把无目标构建当 PASS”和“存在跨机复现风险”；不支持冷构建、干净 clone 或其他机器成功/失败的实际结论。layer34 D0 的验收要求新 clone 构建且日志带 clone commit（`:105-110`），它仍是开放的机械验收项。文档表格还写“各产出五个目录一行”（layer5 `:45-55` 附近），但其 lakefile 问题表实际列出七个候选目录（`:21-31`）；应明确 E1 覆盖范围/行数，避免验收口径歧义。

## 输入充分性与运输核对

当前的倒推拆分在**义务名目**上足够，但尚不足以从 G4 推到 G0：

1. 目标是原始 `q₀ ≤ B`，新六路图将其固定为 G0，并声明不能换目标（`backward-paths-2026-10-23.md:14-24`）。G1 需要同一合法输出的下界与已认证上界，G2 需要 native q ↔ 联合对象 ↔ 原始合法输出，G3 需要 cQ3/cQ4 操作、局部/全局相容与同列 log-Kummer 路径，G4 需要明确输入、箭头端点、允许选择、归一化、商保留数据（`:26-54`）。这些是充分的“待证明义务清单”，不是现成输入。
2. 目标所在类型/transport 当前只在接口层可表达。`EtaAlg` 中 `etaAnab`/`etaQ` 通过 `B.val.C →ₗ[ℝ] ℝ` 作映射比较，定理精确消去到 `logVol` 等式（upstream `EtaAlg.lean:142-153`）；但将实际 Θ-link 的输入 BPS、Hodge theater、原始 Ind 选择送进同一个 `out` 与 `logVol` 的数据来源，未由这些签名自动提供。`PATH.md:80-91` 明说现有 W 系列为玩具层，未构造真实 log-shell、prime-strip、Θ-link 或 `det^{⊗M}`；`round-report.md:13-22, 33-54` 也将玩具到真实对象、合法执行两项列为断口。
3. 允许运输的来源缺口不是单纯图形问题。`handoffs/core-support-2026-10-22.md:20-35` 禁止把域同构叫 Θ-link、把扩大后的线性自同构集叫原始允许重构、或把抽象反例叫 IUT 反例。layer2 的阻塞表要求环级认同、权重、`c` 与 `S` 的依赖分别核查（`backward-paths-layer2-2026-10-23.md:90-120`）；layer34 的 A6/A7 以反例判定是否有限指数足够、是否存在 `S`-依赖（`:71-85`）。即使机械上有依赖链，也必须保留这些真实来源对象及 action 才是合法运输。

## 哪些可以机械验收，哪些需要数学突破

**可机械验收**：固定 commit/source hash；文献和 Lean 签名的行号；候选包是否有目标、lakefile/toolchain/manifest、绝对路径；干净克隆显式目标构建的进程结果；warning/error/axiom 原始日志；有限声明导出和 dependency DAG；PATH 声明与实际交付目录一致；对 P2 量词或 P3 紧致性设计写出有限反例。layer34 对这些明确设了交付格式和失败首项（`:100-130`）；本次 Git 检索复核了其绝对路径 claim。

**需要数学/来源突破**：从原始输入实际构造 `J` 或 `Jε`；证明 (9-1) witness 存在而不是将其字段化；构造真实算法执行并证明输出属于原文允许族；同步 native q 与同一输出的 `logVol`（含 local/global、tensor/determinant/log-link 的同源归一化）；为 P3 找到真实参数空间、闭约束、USC 和全族有限可满足性；为 P4 证明 obstruction 的目标系数、零障碍与联合对象存在之间的等价；为 P5 给出弱化命题推出原 G0 的证明。layer5 的 E2–E5、layer34 的 D1–D7 不会靠编译成功自动完成这些。

## 最短有效路径建议

若目标是**只交一个诚实可检验的中间产物**，最短路径是 P6：显式加入 `hWall : Wall D A`，调用源码已有的 `variant_of_wall`；验收该定理只是条件推论，标题/摘要标明 `(9-1) assumed`，不标作 G0 已证。这几乎纯机械，而且源接口已给出实际条件链（`EtaAlg.lean:169-200`）。

若目标是**无核心假设地推出 G0**，最短的必要链不是 P6，而是：

```text
实际来源构造 (ι,S) 属于原文允许的 η 执行
        + 对同一个输出证明 logVol(out ι S) = qPilot.lhs
        + 对同一输出证明 logVol(out ι S) ≤ B
        → qPilot.lhs ≤ B  (G0)
```

第二项经 `etaAnab_eq_etaQ_iff` 等价于 (9-1)；故这一短链暴露出必须解决的目标而不是绕开它。若只要求任意 ε 的原始证明，可改为同一族 `Jε` 的下界和统一上界，但族的真实允许性与误差趋零也要构造。现阶段最有用的下一步是把 P6 的条件式与真正的上游义务并列管理，并优先设计一份**非字段化**的原始 `η` witness 来源/执行规格；任何 toy 或构建工程只能作为规格检查，不能作为该来源证明。

## 本轮主线接入倒推图

本轮主线的 `Boundary.ProjectiveComparison` 候选按其目标方向，定位为 G3 的**局部工具**：共享的 Kummer 系数幂作用可导出交叉赋值关系和二次标签刚性，同时通过负控制标明不同 anchors 会丢失绝对尺度。此处仅记录主代理提供的定位，不声称我已验过该新 Lean 文件或其构建/导出证据。即使该局部步骤经主线验收，也只补上“系数作用 → 局部交叉关系/标签约束”一段，不能自动 transport 到原始 eta 对象：

- **OPEN — 真实 η 执行来源：** 从原始输入构造实际 `(ι,S)` 与合法 algorithm run，不能以 `EtaAlg.out` 或 `realisation` 字段代替。
- **OPEN — 绝对 volume 标尺：** 把局部赋值/标签约束接到同一原始输出的绝对 log-volume，固定 anchor 的绝对尺度与 tensor/determinant/log-link 归一化。
- **OPEN — G0：** 在同一真实允许输出上取得目标读数及其独立上界，推出 `q₀ ≤ B`；局部 Kummer 刚性本身不是这一不等式。

因此 projective 局部工具可插入倒推图的 G3/G1 之间作为桥梁候选，但不关闭 G2 的来源构造、G1 的绝对读数/上界或 G0。

以上为路径交付审查，不判定 IUT 原论证真伪，不宣称解决原始 gap。
