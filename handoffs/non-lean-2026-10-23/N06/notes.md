# N06 — 归一化、平均与体积换算台账

状态：`STATIC_COMPLETE`（换算条件草稿）。**本表全部公式标 `UNVERIFIED_MATH`**：它们是待验证的草稿，
不是已证恒等式；带精确有理数的例子标 `EXPERIMENTAL`。每行都写清"还缺什么"，缺就写 `UNRESOLVED`。

约定：`source_path` + `line_or_page` 指向 `research/round2-source-cache/` 的检索文本（行号）或外部仓库（`path:line`）。
本表只补**仍未接上**的换算，不重写已有讨论。

## 台账（10 行，见 `normalizations.csv`）

1. **`R^val` pilot ↔ `R^ss` pilot**：`R^ss` 的 pilot 取 `M = 1·S` 所在的体积等价类，`η_q` 的 pilot 取 `{q_v O_v}`
   沿对角线嵌入所得的类。**缺**：两个 pilot 之间是否存在一个被原文确定的实数换算因子；原文只给"体积相同即同类"。
2. **体积商 `V^C(I_v)/∼`**：`T ∼ T'` ⟺ `vol(T) = vol(T')`。**缺**：`vol` 用哪个 Haar 归一化；这决定 1) 的换算因子。
3. **固定 1-column**：`M = 1·S`，`1 ∈ N`。**缺**：`N` 的作用与 `S` 索引的关系（原文 3.11 的 `Ind1/Ind2` 只说明"什么在作用"）。
4. **局部→全局权重**：`q` 侧 `{q_v O_v}` 是逐位给的，`R^ss` 侧只有一个实数线。**缺**：从逐位体积到单一实数的权重（位置数？归一化因子？）。
5. **有限标签平均**：`|F_l|` 索引平均 vs 轨道平均。对应 Lean 侧 `LabelNormalization.averageOverLabels_eq_averageOverOrbit`，
   **仅在 `hAct : Bijective (g ↦ g • base)` 时相等**（`LabelNormalization.lean:165-169`，文件自述见 `:84`、`:224`）。
6. **零标签 vs 非零标签**：同一文件在 `ZMod 3` 上给出 2 vs 1 的反例（标签集不是轨道）。**缺**：原文哪个归一化对应"零标签"情形。
7. **轨道/稳定子重数**：平均要对轨道而不是对群元素求，否则稳定子会把权重乘偏。**缺**：原文没给稳定子重数的显式因子。
8. **Haar 参考格**：`ResidueHaar`、`PadicPrincipalHull` 的声明是 `ℚ_p^n/Z_p^n` 模型；**缺**：把该参考格换成真实系数环 `O_{F_v}` 时 Haar 测度的换算。
9. **有限商计数**：`#(O/p^kO)` 型的计数在玩具里可算（N09），**缺**：原文用的是哪一族有限商（N04 结论：仓库没有 `Finite (Tensor …)` 定义）。
10. **实数 log 与 p-adic log**：`localLog` 是 `ℚ_p` 上的 `∑'`（`CoreTransport/Basic.lean:9-10`）；`logVol` 是实数值。
    **缺**：两者之间的换算不存在于仓库；任何"相等"都必须经过一层取值函数，不能默认同一。

## 三条红线
- **不把浮点接近当恒等式**：本表不给任何小数近似当作证据；需要数值的场合用有理数或精确 p-adic 计算（N09 的做法）。
- **不预设分母非零/正性**：凡出现除法的行，条件列写明 `M ≠ 0` 之类的必要条件（例：`comparison_well_defined` 的 `hM : M ≠ 0`）。
- **不把"两套 log 相等"写成已证**：第 10 行留 `UNRESOLVED`，因为仓库里根本没有连接它们的映射。
