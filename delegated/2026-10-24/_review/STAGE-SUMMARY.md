# 本批任务阶段性汇总（2026-10-24）

只写已经发生的事。**没有**任何任务升级为已证数学，**没有** fact-tree 准入，**没有**核心 GAP 关闭。

## 1. 交付状态

| 任务 | 状态 | 预检 | 主线独立哈希复核 |
|---|---|---|---|
| T003 | RESEARCH_ONLY | `PACKAGE_COMPLETE` | 21/21 |
| T008 | RESEARCH_ONLY | `PACKAGE_COMPLETE` | 12/12 |
| T065 | RESEARCH_ONLY | `PACKAGE_COMPLETE` | 17/17 |
| T066 | RESEARCH_ONLY | `PACKAGE_COMPLETE` | 7/7 |
| T097 | RESEARCH_ONLY | `PACKAGE_COMPLETE` | 11/11 |
| T002 | 未成形（`.tmp` 与既有 fact-tree 逐字段相同，零增量） | — | — |
| T015 | SUMMARY 已有，`delivery.json` 未落 | — | — |
| T021 | 快照工程已构建（8782 jobs, exit 0）但未交 delivery | — | — |
| T049 | 有 7 次 build 日志与源码，未交 delivery | — | — |

合计 **68 个 artifact 哈希由主线逐条重算，全部一致**。
`check_delivery.py` 的 `PACKAGE_COMPLETE` 只表示**材料与哈希**，不代表数学、公理、语义或编辑器观察。

## 2. 修掉的两个真实工程缺陷

### 2.1 mathlib 被钉死在本机桌面路径

`core-log`、`core-compactness`、`nonarchimedean-ring`、`pilot-shadow` 四个包写的是
`require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"`，
他人（包括审查方）无法解析依赖。已改为标准 `require mathlib`（走已提交的 `lake-manifest.json`）。

从**空构建缓存**实测：

```text
core-log           lake build CoreLog         exit 0  3047 jobs  311.9 s
core-compactness   lake build CoreCompactness exit 0  1627 jobs   36.7 s
nonarchimedean-ring lake build Candidates     exit 0  1770 jobs   52.0 s
```

提交 `71358fd`（分支 `fix/portable-mathlib`）。

### 2.2 core-kummer 的构建图残缺（更严重）

包内 **30 个 Lean 模块，lakefile 只声明 7 个 roots** → 23 个模块是游离的，
`lake build` 从不编译它们，永远没有 `.olean`，任何 import 它们的文件必然失败。

这是 T008 的 **A21**（`Boundary/DecompositionBridge.lean` 无法核验）的真正根因，
也是 `LaurentPoint.lean` 无 olean、"相邻欠账"的来源。

补全 roots 后从零构建实测：

```text
lake build ContinuousKummerTheory   exit 0   8767 jobs
lake build Boundary                 exit 0   8789 jobs   504.2 s   (-DwarningAsError=true)
```

`DecompositionBridge.olean` **首次生成**（187120 B）。提交 `764c7b3`。
**只补构建图，未改动任何源文件、命题或证明。**

> **重要限定（由审查官 C 指出，主线核实成立）**：`764c7b3` 只挂在分支
> `fix/portable-mathlib`，**不是 `explore/correspondence` 的祖先**。
> 因此上面这条"已修复"**仅在 `fix/portable-mathlib` 分支上成立**：
>
> - `git show HEAD:candidates/core-kummer/lakefile.lean` 仍只有 **1 行**（旧版）；
> - 主工作区那个补全版是**未跟踪修改**，没有随任何提交进入当前分支；
> - 主工作区的 `Boundary/DecompositionBridge.olean` **仍不存在**（实测 `Test-Path` = False）；
> - 主工作区仍缺 7 个 olean。
>
> 所以 **T008 的 A21 在主工作区仍无法核验**。要让它成立，必须把
> `fix/portable-mathlib` 合入当前分支，或在该分支内重跑。
> 这条更正来自对抗性审查，不是自查——我方此前把它写成无条件"已修复"，是不准确的。

## 3. 三个必须记住的交付格式坑

记在 `_review/delivery-format-pitfalls.md`：

1. **自引用哈希**：`delivery.json` 把自己列进 `artifacts` → 哈希永不相等 → 包恒不可通过（T003 实例）。
2. **空构建**：`lake build` 无参返回 0 但 `Nothing to build`，等于什么都没验。
3. **构建图残缺**：见 2.2。

另有 T065 报告的第四类：预检要求登记**预检自身日志**的哈希 → 自指不动点；
且 PowerShell `>` 写 UTF-16、Python 在 Windows 把 `\n` 翻成 `\r\n`，都会让哈希永远对不上。

## 4. 独立审查抓到的实质错误

### 4.1 T008 的箭头计数虚高（审查官 A）

交付方报"已构造 18 条"。A 核出 **A03 是真 `rfl`**（定义展开不计构造）、**A09 是 A08 的展开式**（应合并），
应按**约 16 条**计。A 同时明确"交付方标了 `rfl` 是诚实的，问题只在计数，不在诚信"。

另指出 A14/A15 的证明体只有 3 行，实质数学在 `Specialization.lean:147-188` 的通用引擎——
引理委托是正常方式，但台账不可让人误以为方块交换性在 A14 内部证出。

见 `_review/A-evidence/T008-erratum.md`。

### 4.2 T008 关于 `letI` 的论述方向错误（审查官 B，主线独立复现）

交付方写"忘记 `letI` 会**静默落到**另一个作用实例"。审查官 B 用对照探针实测，
主线在 `candidates/core-kummer` 内**独立复跑确认**：

```text
argv:  lake env lean .wt/leti-check/BLetIProbe.lean
exit:  1
error: failed to synthesize
       MulDistribMulAction (↥(decompositionSubgroup F A)) (Mu n (ResidueField ↥A))
```

这是**编译期硬错误**，不是静默换实例。原因是工程里没有可被误落的第二个目标实例
（`Basic.lean:86` 的作用群是 `Gal(Ω/K)` 不是 `Gal(κ/k)`；`Decomposition.lean:140` 的 `muAction` 是 `def` 不入实例搜索）。

性质：**机制解释错误，不是事实伪造**。它不影响 T008 其余自述（审查官 B 复核确认其余 4/5 正确、23 条无错标）。
见 `_review/A-evidence/T008-erratum-letI.md`。

### 4.3 主线自己的记录被驳回（值得记下的纪律）

我给主线自己写的一份重放记录只有叙述性数字（无原始产物），被审查官 A 拒绝：
"不能对主线放宽"。补上 `stdout.jsonl`（5817 B）、`stderr.txt`、`exit.txt`、`timing.txt`、`argv.txt` 后才成立，
并借此发现我写错了数字（声称 58 条 information，实际 **18 条**）。

A 复核后追加行号级核验：18 行 `pos.line` 恰为 237–254，与源码 `#print axioms` 逐行全等，
确认是真实 elaborator 输出。见 `_review/A-evidence/independent-replay-core-germ.md`。

## 5. 一条被主线核实的关键量词事实（T097）

`reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean:173-175` 原文：

```lean
def Wall (D : InitialThetaData.{0}) (A : Wall.EtaAlg D) : Prop :=
  ∀ (h₁ h₂ : A.Side) (_gl : BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂)),
    ∃ (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D), A.etaAnab ι S = etaQ D
```

**∀ 在外、∃ 在内、`ι` 绑在 `S` 之前**；且该文件自注 "A hypothesis, never assumed."。
审查官 B 独立复算禁式（`for all/every/any S`、`any such S`、`arbitrary S`）在 LANA / IUT III / EtaAlg **命中数全为 0**。

即：**不存在"所有 S 上不变"的声称空间**。这与此前几轮反复纠正的"把存在性当成全族不变"同一个坑。

## 6. 仍然开放的东西（一条都没关）

- T008：A20（非代数闭 / 非有理点时 `decompositionMap` 满射未证）、A22（tempered Π out of scope）、
  A23（Wall (9-1) 是结构字段假设）。
- T065：5 项 UNRESOLVED（strip / coric / link / 各环境 `kum` 源头任取 / arc 无构造声明）；
  22 个字段**全部**由 structure 提供，定义生成 **0**。
- T097：U1（LANA 自陈 (9-1) 无证明）、U2（Cor 3.12 原文只是成员关系，不能读回 IUT）、
  U3（Ind3 范围 LANA 与 Lean 不一致，只记录不裁定）、U4（`EtaAlg.out` 是裸字段）。
- 核心 GAP 全部 OPEN；没有任何命题因本轮工作成为已证。
