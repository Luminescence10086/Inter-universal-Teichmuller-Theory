# T008 · GAP

状态：**OPEN**（不关闭任何核心 gap；本文件只记本任务自己遇到的、未在本任务内解决的项）

## G1 — `Boundary/DecompositionBridge.lean` 无法在本工作区核验（阻塞 A21 的证据层级）

**首个缺失物**：`candidates/core-kummer/.lake/build/lib/lean/Boundary/DecompositionBridge.olean`。

- 该文件在 `baseline.json` 的 `files` 列表中，SHA256 `1bc8a3e3986ce953e7b2f3d378119c0e6baed7366ba12c2bb4ee819027d4984a`，4321 字节，工作区实测一致。
- 但 `.lake/build/lib/lean/Boundary/` 下 **只有** `AnchoredComparison / DiscreteValuation / FinitePlace / Frontier /
  PrecisionLoss / ProjectiveComparison / ReducedComparison / ThetaGermTransport` 八个 `.olean`，**无 `DecompositionBridge.olean`**。
- 尝试：直接 `import Boundary.DecompositionBridge` 到 `probe/T008Probe.lean`，Lean 报
  `error: object file '...\Boundary\DecompositionBridge.olean' of module Boundary.DecompositionBridge does not exist`，exit 1。
- **为什么本任务不自行构建**：`lake build` 会写 `candidates/core-kummer/.lake/`，那是**主工程**的构建目录，
  且 PROTOCOL 明确要求本机重型 Mathlib 编译走排队串行、并禁止改主工程依赖/产物。T008 的写入范围只有
  `delegated/2026-10-24/T008/`。
- **因此**：`CoreDecompositionBridge.reducedClass`、`residue_kummer_eq_of_reduced_restrictions_eq`、
  `principal_eq_of_reduced_comparison_and_bound` 三条在箭头表中记「仍为假设（未核）」（A21），
  尽管其源码文本存在且形状合理。**源码存在 ≠ 已编译 ≠ 已验收。**
- 下一步（交给能写主工程或已排到队尾的任务）：在 `candidates/core-kummer` 下
  `lake build Boundary.DecompositionBridge`（或 lakefile 增加对应 `lean_lib` 目标）后重跑本目录 `replay.ps1`，
  再按 A21 的重命名把该行升级。本文件不预判升级结果。

## G2 — `decompositionMap` 满射的适用范围（阻塞 A20）

已在 A16/A20 记账：已证明的满射需要 `[IsGalois F Ω]` + `[IsAlgClosed Ω]` + `[Algebra.IsIntegral k κ]` + `hres`。
**未尝试也未能构造**：非代数闭闭包、或残值不在 `k` 内（非 `k`-有理点）时的任何满射/商识别。

需要注意的**不能做的事**：不能把 A16 的 `hres` 改写成「普遍成立」的假设后宣称右腿是 inflation。
`research/core-boundary-2026-10-24/source-audit.md:32-51` 已独立记过同一限制（「surjectivity is the rational-point case
supplied by `hres`, not an unconditional theorem」），本任务复核后与之一致。

## G3 — `reduceMu` 的可逆性（A19）

工作区**不存在**任何 `Injective` / `Surjective` / `≃*` 形式的 `reduceMu` 声明。
本任务**没有**尝试证明或反证它，因为 A18 的反射路线不需要它（`Boundary/ReducedComparison.lean:4-5,22-23` 明说）。

留作 OPEN：若后续任务需要「从左腿反推源类」，那需要 `R := 限制 + 系数约化` 的反射结果，
这是**独立于**本方块的新义务，不能从 A14 直接得到。
`research/core-boundary-2026-10-24/source-audit.md:53` 也把该结论列为「would require a separate reflection result」。

## G4 — 上游 pinned 源码与工作区副本的差异（不影响本任务结论，但影响跨机复现）

- `candidates/core-kummer/ContinuousKummerTheory/Kummer/Decomposition.lean` 与
  `research/core-kummer-2026-10-24/continuous-kummer-pin/…/Decomposition.lean` **字节相同**
  （SHA256 `b7a67da60e61998d631201b3053aadea387993c68984dd1e14a3f5d9d446b7a6`，11500 字节）。
- `DecompositionSurjective.lean` **不同**：工作区版 `88f59d79…`（25255 字节）vs
  `reviews/core-round/external/continuous-kummer-theory` 版 `ac1e91c8…`（25240 字节），
  `git diff --no-index` 显示 10 处改动，全部是「新版 Mathlib 适配」性质
  （`if_neg/if_pos` → `ite_eq_right/ite_eq_left`、`haveI` → `have`、`erw`、`isIntegral_algebraMap_iff` 显式参数）。
  **语义未变**，但**文件名相同不代表版本相同**（任务卡原话）。本任务所有 `#check` 均在工作区副本上跑，
  SHA 已在 `delivery.json` 绑定。

## 没有列入 GAP 的项

- C2 的连续性证明本身：源码 `Decomposition.lean:107-131` 有完整证明，本任务 `#check` 到其确切类型，
  **不构成 gap**，只是「带前提的已构造」。
- A14/A15 的方块交换：同等，已构造，前提已逐条列在箭头表。
