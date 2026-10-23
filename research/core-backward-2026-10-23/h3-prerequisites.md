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

- **〔已核〕Step (x) 尾部**，txt 10904–10922：原文自称的归一化是
  「the **procession-normalized** mono-analytic log-volumes [i.e., **where the average is taken over
  `j ∈ F_l^⋆`**] of Theorem 3.11, (i), (a), (c)」，其性质被明写为：
  (i) 对 **(Ind1)、(Ind2) 不变**；(ii) 把 **(Ind3) 化为一个"inequality [from above]"**；
  (iii) 这些平均来自 `F_l^⋆` 在 theta 值标签上的对称作用（10917–10922）。
  **这条对 H3 的含义**：原文自己的"粗化"读数就是一个**平均**，而且它在 Ind3 下只有**上界**而非等式——
  这与 `design-h1-h3.md` 里"形式商 vs coarse 影子"的分层完全吻合，也解释了为什么 xi-f 是估计而 xi-d 要求
  "suitably normalized"。
- **〔已核〕Remark 3.1.1(ii)**，txt 5512–5529：这是原文**真的写出**的归一化——单点权重
  `[K_v : (F_mod)_v]^{-1}`（5514），以及求和时的归一化权重
  `1/([K_v:(F_mod)_v]) · ∑_{V_mod ∋ w | v_Q} [(F_mod)_w : Q_{v_Q}]`（5519–5524），并给出原则：
  「normalized so that multiplication by `p_{v_Q}` affects log-volumes by addition or subtraction …
  of the quantity `log(p_{v_Q})`」（5525–5529）。
  **注意**：这是 `E/N` 侧的权重，**不是** (xi-d) 的 `j` 归一化；两者不可混用。
- **〔已核〕(xi-d)**，txt 11022：`[suitably normalized, with respect to j ∈ |F_l|] log-volume`——
  索引是 **`|F_l|`**（集合），与 Step (x) 的 **`F_l^⋆`**（群）**不同**；"suitably" 始终未被指定。
  两处是否为同一个归一化，原文**没有**声明。
- **〔已核〕Prop 3.9(iii)**，txt 7080–7090：全局 log-volume 等于由 `J` 决定的 arithmetic line bundle 的
  degree，但仅「relative to a **suitable normalization**」；Remark 3.1.1(ii) 的公式是**候选**，但原文没说是同一个。
- **要补的证明**（三条，按难度）：
  1. 把 (xi-d) 的 `j ∈ |F_l|` 归一化写成显式函数，并证明它与 Step (x) 的 `F_l^⋆` 平均**相容**
     （或给出二者差的显式界）——这是 `vQ = q₀` 有确定含义的前提；
  2. 证明 Prop 3.9(iii) 的"suitable normalization"就是 Remark 3.1.1(ii) 那条（给出公式即可，但要引用对齐）；
  3. 在 1、2 之后，才谈得上"同一对象的 native 读数 = 输出读数"这类陈述。

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

本轮新增的一条实质结论：原文**并非没有归一化**——它写出的那条是 **procession-normalized（对 `j ∈ F_l^⋆`
取平均）**，且明说该体积对 (Ind1)(Ind2) 不变、把 (Ind3) 化为**上界不等式**（10904–10922）。这说明原文的
"coarse 读数"本身就是一种**平均意义上的读数**，而不是某个被指定的单点值。于是 (xi-d) 的
`[suitably normalized, w.r.t. j ∈ |F_l|]` 所缺的不是"随便一个约定"，而是**与这个平均的相容性证明**——
这正是上面的第 1 条义务。
