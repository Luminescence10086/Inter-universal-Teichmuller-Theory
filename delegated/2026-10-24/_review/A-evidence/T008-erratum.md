# T008 台账勘误（主线据独立审查意见追加，不改原件）

日期：2026-10-24。来源：独立审查官 A 的 `_review/A-evidence/T008-round3.md`（判定 `PASS_WITH_FINDINGS`）。
本文件**不修改** `delegated/2026-10-24/T008/` 内的任何原件——那属于交付方的审计链，
主线不在别人的交付里改数字。本文件是把审查意见落成**可引用的勘误表**，供后续引用时按本文口径。

## 1. 必须修正的计数口径（唯一实质问题）

交付方报"已构造 18 条（A01–A18）"。A 的核查结论：**应按约 16 条计**。

| 条目 | 原件写法 | A 的核查 | 处置 |
|---|---|---|---|
| A03 | `decompositionMap_apply : decompositionMap σ x = σ • x`，依据 `rfl` | 确是 `rfl`；交付方**自己标了 rfl**，披露诚实 | 定义展开不计入"构造"，应降为 A02 的注记 |
| A09 | A08 的"一般引擎" `specMu` | 源码 L150 `reduceMu := specMu …`，**同一 def 的两种写法** | 与 A08 合并，否则重复计数 1 条 |
| A01 | `Subgroup.subtype` | Mathlib 现成构造 | 不降档，但应标注归属 |

**重要区分**：A 明确写"交付方标了 `rfl` 是诚实的，问题只在计数，不在诚信"。本勘误不质疑交付方诚信，
只纠正可引用性。任何后续文档引用 T008 时，**"18 条已构造"应按"约 16 条"表述，或明确注明含 A03/A09 两项定义展开**。

## 2. 必须披露的引理委托（A14/A15）

交付方标 A14（方块交换 `decomposition_kummer`）与 A15（值版本）为"已构造（带前提）"，
这一标注**本身没错**。但 A 指出：两者的证明体**只有 3 行**，实质数学在
`ContinuousKummerTheory/Kummer/Specialization.lean:147-188` 的通用引擎（42 行）。

- 引理委托是正常证明方式，**不是造假**。
- 但台账不得让人以为方块交换性是在 A14 内部证出来的。引用 A14 时应同时引 `Specialization.lean` 的引擎。

## 3. 措辞修正（`letI` 与 `muAction`）

交付方 §1.3 写"忘记 `letI` 会使语句变成不同命题"。A 核出**机制方向对、措辞偏重**：

- 竞争实例真实存在（`ContinuousKummerTheory/Kummer/Basic.lean:86-91` 的 `Gal(Ω/K)` 实例）；
- `muAction` 是 `def` + `@[implicit_reducible]`，**不是 `instance`**——这正是必须显式 `letI` 的机械原因；
- 生产代码实测 **7 处** `letI := muAction`（`Decomposition.lean` L165/167/183/188/202/208 与 `KummerClass.lean:174`）；
  原件引的 `:165,183,188,202,208` 行号不精确但方向对；
- **实情**：两个作用在数值上恰好一致（因为 A03 是 `rfl`），真正的风险是 **elaboration 消解到哪个实例**，
  不是"命题变了"。

引用时请写："必须经 `letI` 显式指定实例，否则 elaboration 可能消解到竞争实例"，不要说"变成不同命题"。

## 4. 计数口径的次要提示

原件称 probe 跑出 23 条 `#check`，但 stdout 里以 `@` 开头的只有 **18** 条——
因为 5 个目标以普通常数形式打印。**23/23 成立**，但按 `@` 计数会误判为 18。
引用时不要用 `@` 前缀数当条数。

## 5. A21 已由主线解除（另见 `T008-A21-unblocked.md`）

`Boundary/DecompositionBridge.lean` 此前无 olean 的真实根因是包内 30 个模块只声明了 7 个 roots
（23 个游离模块）。已在提交 `764c7b3` 补全构建图，从零构建 `lake build Boundary` exit 0（8789 jobs，504.2 s），
`DecompositionBridge.olean` 首次生成（187120 B）。

**但这只把 A21 从"不可核验"提升到"可核验"**，不自动升为"已证"：
T008 原本要判断的是该文件的 `reducedClass` / `residue_kummer_eq_of_reduced_restrictions_eq`
在**语义上是否足以支撑 A18 的反射单射**，那是审查判断，不是"文件能编译"。

## 6. 本勘误不改变的东西

- T008 仍为 `RESEARCH_ONLY`；不授予 fact-tree 准入。
- A20（非代数闭 / 非有理点时 `decompositionMap` 满射未证）、A22（tempered Π out of scope）、
  A23（Wall (9-1) 是结构字段假设）三项**一条都没被解决**。
- 核心 GAP 全部保持 OPEN。
