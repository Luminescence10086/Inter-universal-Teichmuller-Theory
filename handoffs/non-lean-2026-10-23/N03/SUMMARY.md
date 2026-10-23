# N03 — 核心目标的量词、类型与依赖清单

状态：`STATIC_COMPLETE`（目标规格草稿；不声称 (9-1) 成立）

## 一句话
(9-1) 是：**固定数据后，存在某个 `S : Ind3 D` 使 `etaAnab ι S = etaQ D`**；在 Lean 侧它等价于一个实数等式
`logVol(out ι S) = qPilot.lhs`。目标是存在型，不是全族不变型。

## 三条必须分开的条件（`obligations.csv` 有 9 行）
- **充分**：造出一个 `S` 使标量方程成立（O1）——仓库里**没有**这样的 `S`，`logVol(out ι S)` 从未对任何构造出来的 `S` 算出。
- **必要**：两图相等 ⟺ 在 pilot 处相等（O2，`eta_eq_eta_iff`）；`Ind1/Ind2` 相容（O3）；`ι` 先于 `S` 量化（O4）；
  两套 pilot 归一化必须对齐（O6，留给 N06）。
- **更强但非必需**：读数在整个族上不变（= W5/W7）。本工程已用 `existence_does_not_force_invariance` 证明它不被蕴含，
  写成它会把目标换成另一个问题（O5）。

## 到 Cor 3.12 / abc 的依赖
单列为 O8、O9：Cor 3.12 还需要 xi-d…xi-f 的 log-volume 计算；abc 还需要高度比较与算术识别。
**两条都不因 (9-1) 而成立**，本件不预设它们已完成。

## 出处
原文：`LANA-interim-report-2026-07.txt` §9.2，p.45–46，行 2138–2141（"there exists some suitable S such that η_q = η^anab_S"）。
Lean：`Iut/Wall/EtaAlg.lean:151`（`etaAnab_eq_etaQ_iff`）。全部为 `SOURCE_FACT`，除 O7/O9 标 `UNRESOLVED`。

## 未做
没有形式化 `R^ss` 的商结构，没有构造 `Ind3 D` 的元素，没有算出任何 `logVol`；`target.md` 是规格，不是证明。
