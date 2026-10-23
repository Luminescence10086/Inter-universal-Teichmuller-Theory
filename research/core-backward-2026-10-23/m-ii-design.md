# M-ii 的类型设计：`M` 何时被确定、何时不被确定

日期：2026-10-23。状态：**设计 + 玩具形状**，非结论、非 fact-tree。核心 GAP 保持 OPEN。

## 义务回顾（来源已核）

**(Ob3-2)**，txt 8084–8101：`"det^{⊗M}(−)"` 里的 **M** 是

> 「the **[uniquely determined]** positive integer [cf. the positive integer "N_E" that appears in the final
> portion of the discussion of Remark 3.1.1, (iv)] such that this operation maps an arithmetic line bundle
> to the `M`-th tensor power of the arithmetic line bundle」

两个要点：**唯一性被断言**、**与 `N_E` 的联系只是 `cf.`**。义务是三处 `M` 同一：hull 的 `det^{⊗M}`、
q-pilot 侧被比较的 `M` 次幂、`(Ob4-1)` 的 degree-M Frobenius。

## 设计：唯一性只能通过"读数非零的探针"取得

因为 `M` 是通过**读数**（log-volume）被观察的——对象层的 `a^{⊗M}` 与 `a^{⊗N}` 是否相同，最终要落到读数上——
所以 `M` 的确定性完全取决于**探针**：

设 `R` 为读数、`x` 为探针，则

```
R (x^M) = R (x^N)  ⇒  M · R x = N · R x  ⇒  (M − N) · R x = 0
```

于是：

- 若 `R x ≠ 0`（**非挠探针**），则 `M = N`——`M` 被确定；
- 若 `R x = 0`（例如 `x` 是单位根、或 `x = 1`），则对一切 `M, N` 都有 `R (x^M) = R (x^N)`——
  **`M` 完全不被确定**。

这一条正是 (Ob3-2) 的"cf. `N_E`"为什么不够的原因：**认同需要指明探针**；若探针的读数为零，任何两个指数都
给出相同的读数。反过来，一旦探针的读数非零，(Ob3-2) 的"uniquely determined"就有了实际内容，且三处 `M`
的同一性化归为**同一探针上的读数相等**。

## 玩具（W9）证什么、不证什么

在 `ℚ_[3]` 上，取探针 `x = 4`（W8 已证 `‖localLog 4‖ = 1/3`，故 `localLog 4 ≠ 0`）：

- `power_reading_injective_on_probe : localLog (4^M) = localLog (4^N) ↔ M = N`——在非挠探针上指数唯一；
- `exponent_determined`：若对所有探针读数都相等，则 `M = N`（在 `4` 处取即可）；
- `not_determined_by_torsion_probe`：取 `x = 1`（读数为零），则对任意 `M ≠ N` 仍有
  `localLog (1^M) = localLog (1^N)`——**挠探针什么都不确定**。

**不证**：三处 `M` 在原文对象上确实是同一个。本玩具只说明"唯一确定"**需要什么条件**，以及为什么
"cf. `N_E`"不足以代替它；真正的同一性仍需在 `det^{⊗M}` 的真实对象与 `(Ob4-1)` 的 Frobenius 上对齐。

## 与 M-i / M-iii 的关系

- **M-i** 说：除回需要 `τ = 0`；
- **M-ii**（本文件）说：指数需要"非零读数的探针"；
- **M-iii** 说：读数本身需要归一化对齐（`|F_l|` 索引 = procession 平均）。

三者合起来是一句话：**任何"读数上的相等"都必须先说明它用哪个读数、在哪个探针上、按哪个归一化。**
三条缺一，等式就没有确定含义。

## 仍未解决

1. 真实对象上三处 `M` 的同一性（需要 `det^{⊗M}` 的对象层构造 + `(Ob4-1)` 的 degree-M Frobenius）；
2. 若 `M` 由"足够大的正整数"（(Ob3-2) 后文的"sufficiently large"）刻画，则唯一性还需说明"足够大"如何选定；
3. 探针在原文中究竟是哪一个——`N_E`、q-pilot 的 `−|log q|`、还是某个 1-column 的不变量。
