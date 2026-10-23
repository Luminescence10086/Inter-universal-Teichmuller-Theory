# H3 前置：`M` 的唯一性与两处未写出的归一化

日期：2026-10-23。状态：**义务清单 + 玩具形状**，非 Lean 结论、非 fact-tree。核心 GAP 保持 OPEN。

本文件把 `handoffs/core-backward-2026-10-23/M2/` 的账面发现转成**必须补哪些证明**，并对每条给出该文件
可核对的行号。标注规则：**〔已核〕**＝本轮我自己回原文逐字读过；**〔M2〕**＝M2 的定位，本轮未独立复核。

## M-i：原文没有"除回 `M` 次 tensor power"的映射

- **〔已核〕(Ob4)**，txt 8135–8144：原文只说这个"稍作修改的目标"「does not result in any substantive
  problems such as, for instance, an indeterminacy arising from confusion between a given arithmetic line
  bundle and its `M`-th tensor power」——是**断言无害**，没有映射、没有定量界、没有不变性陈述。
- **〔已核〕(Ob4-3)**，txt 8185–8189：对重构出的非 tensor-power Frobenioids 与给定 tensor-power 副本之间
  只到「a "tensor-power-twist indeterminacy"」，随后断言「we shall ultimately [e.g., in the context of
  Corollary 3.12] only be interested in **estimates of log-volumes**, such tensor-power-twist indeterminacies
  will not have any substantive effect on our computations」。
  **注意措辞**：这里说的是 **estimates**，不是精确等式；把它当成精确相等会用错原文。
- **要补的证明**：给出一个把 `M` 次 tensor power 的读数送回原读数的**具名操作**，并证明
  (i) 它与 twist 不定性相容；(ii) 它只改变一个可控量（否则 (Ob4-3) 的"no substantive effect"没有依据）；
  (iii) 在取 log-volume 之后该量消失（或进入一个显式误差界）。

## M-ii：`M` 只被"唯一确定"，从未被赋值

- **〔已核〕(Ob3-2)**，txt 8084–8101：`"det^{⊗M}(−)"` 中的 **M** 是「the **[uniquely determined]** positive
  integer [cf. the positive integer "N_E" that appears in the final portion of the discussion of
  Remark 3.1.1, (iv)] such that this operation maps an arithmetic line bundle to the `M`-th tensor power of
  the arithmetic line bundle」。
  即：**唯一性有、值没有**；与 `N_E` 的联系只是 `cf.`，不是等式。
- **要补的证明**：证明三处 `M` 是**同一个**——(a) hull 的 `det^{⊗M}` 里的 `M`；(b) q-pilot 侧被比较的那个
  `M` 次 tensor power 里的 `M`；(c) `(Ob4-1)` 的 naive Frobenius functor 的 degree `M`。
  三者若不同，(Ob4) 的"无害"结论不自动成立。

## M-iii：两处归一化被使用但从未写出公式

- **〔已核〕(xi-d)**，txt 11022：`[suitably normalized, with respect to j ∈ |F_l|] log-volume`——**只给限定语，
  没给公式**。
- **〔M2〕** Step (x)（p.181）用的是 `j ∈ F_l^⋆` 上的**平均**；两处是否同一个归一化，原文未声明。
  本轮未独立复核该处，**不可**据本文件宣称二者不同或相同。
- **〔已核〕Prop 3.9(iii)**，txt 7080–7090：全局 log-volume 等于由 `J` 决定的 arithmetic line bundle 的 degree，
  但仅「relative to a **suitable normalization**」，该归一化全文未写。
- **要补的证明**：把 `j ∈ |F_l|` 的归一化写成显式函数（或显式的平均），并证明
  (i) 它与 Step (x) 所用的是同一个；(ii) 它与 Prop 3.9(iii) 的"suitable normalization"相容。
  在这两条之前，`vQ = q₀` 这类陈述**没有确定的含义**（换归一化会改数值）。

## 玩具能说什么、不能说什么

`candidates/core-transport/DivideBackLaw.lean`（待修至可编译；见 W3）只做 M-i 的**形状**：

- 若读数是主单位上的对数，则"`M` 次幂的读数 = `M` × 读数"是可证定理，于是"除回"就是**除以标量 `M`**，
  不需要另设一个映射；
- 同一 `x = 4`、`M = 2` 处，范数读数**不**具备该性质（`‖4²‖/2 = 1/2 ≠ 1 = ‖4‖`），所以"除以 `M`"不是
  无内容的一步，性质也不是任意读数都自动成立。

它**不**说：`M` 的取值（M-ii）；(Ob4-1)/(Ob4-2)/(Ob4-3) 的 tensor-power Frobenioid 上的除回映射；
twist 不定性的行为；以及 M-iii 的任何一条。`ℚ_[3]` 是完备离散值域，`x ↦ x^M` 不是 `det^{⊗M}`。

## 结论

这三条是 H3 的**前置**，不是可选项：只要它们没被证明，(Ob4) 的"无害"与 (xi-d) 的"精确 log-volume"之间的桥
就只有文字、没有对象。**核心 GAP 保持 OPEN**；本文件不构成对任何 IUT 主张的支持或反驳。
