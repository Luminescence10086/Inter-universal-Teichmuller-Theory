# G1 解除记录：Boundary/DecompositionBridge.lean 的 olean 由主线补建

日期：2026-10-24。执行者：主线（非 T008 交付方）。
对应：`delegated/2026-10-24/T008/` 的 **A21** 与它的 `GAP.md` 中"G1 阻塞 A21"一项。

## 1. 交付方当时的处置（正确）

T008 报告：`Boundary/DecompositionBridge.lean` 在 `baseline.json` 里，但工作区**没有 olean**，
因此无法从本工作区核验 `reducedClass` / `residue_kummer_eq_of_reduced_restrictions_eq`，
按"代理自报 ≠ 已验证"记为**假设**而非已构造，并向主线提出补编译请求。

它同时**没有**自行 `lake build`，理由是那会写 `candidates/core-kummer/.lake`、超出其写入范围、
并违反串行编译约定。这个处置是对的：越界写主工程会污染基线，比"少一条已构造"严重得多。

## 2. 主线查到的真实根因（比"缺 olean"更深）

`candidates/core-kummer` 含 **30 个 Lean 模块**，但 `lakefile.lean` 只声明了 **7 个 roots**：

```text
ContinuousKummerTheory : ContH1.Basic, Hilbert90, Kummer.Basic, Kummer.Equiv
ValuationSupport       : KummerValuationSeparation
CoreKummer             : KummerClassValuationBridge, CohomologyReflection
```

其余 **23 个模块是游离的**（`Boundary/*`、`Kummer/Corestriction|Decomposition|DecompositionSurjective|Restriction|Specialization|Values`、
`TateCurvesTheta/*`、`Export*.lean`）。`lake build` 从不编译它们，因此**永远不会有 olean**；
任何 import 它们的文件都会报 `object file ... does not exist`。

所以 A21 不是"这次忘了建"，而是**构建图长期不完整**。同一根因还解释了：
`Boundary/LaurentPoint.lean` 无 olean（审查官 A 称之为"相邻欠账"），
以及 `ThetaGermTransport.lean` 只能靠 `lake env lean <file>` 单独 elaborate。

## 3. 主线修复与实测

`lakefile.lean` 改为把**每个模块都列为 root**，并补 `TateCurvesTheta` / `Export` / `Boundary` 三个 lib。
同时把 `require mathlib from "C:/Users/…/mathlib"` 改为 `require mathlib`（同 `fix/portable-mathlib`）。
**未改动任何源文件、命题或证明**，只补构建设置。

从零构建实测（`candidates/core-kummer` 的空 `.lake`）：

```text
lake build ContinuousKummerTheory   exit 0   8767 jobs
lake build Boundary                 exit 0   8789 jobs   504.2 s   （-DwarningAsError=true）
```

`Boundary/.lake/build/lib/lean/` 现含 **10 个 olean**，其中
`DecompositionBridge.olean` = **187120 B**，此前从未被生产过。

## 4. A21 现在的状态

- `Boundary/DecompositionBridge.lean` **现已可被 elaborator 核验**，且在 `-DwarningAsError=true` 下
  与整包一起构建通过（exit 0）。
- 该文件中的三条声明现可定位：
  - L24 `noncomputable def reducedClass`
  - L35 `theorem residue_kummer_eq_of_reduced_restrictions_eq`
  - L57 `theorem principal_eq_of_reduced_comparison_and_bound`
- **但状态只从 UNDECIDABLE 升为"可核验"，不自动升为"已证"**：
  T008 原本要核的是这三条**在语义上是否足以支撑 A18 的反射单射**，
  那是审查判断，不是"文件能编译"。这一步仍需审查官做。

## 5. 不得据此升级的部分

- 不改变 T008 的 `RESEARCH_ONLY` 状态；不授予任何 fact-tree 准入。
- 不放宽 A20（非代数闭 / 非有理点时 `decompositionMap` 满射未证）与 A22/A23（tempered Π、
  Wall (9-1) 的结构字段）。
- 审查官 A 另指出的**计数口径问题**（A03 为 `rfl`、A09 与 A08 重复，构造数应约 16 而非 18）
  与此处无关，仍需交付方或主线修正台账。
