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
- **〔已核〕两条具名归一化**，txt 7000–7010 与 7034–7039：
  - **packet-normalization**（7000–7002）：把 `M(−)` 的元素乘 `e = 2.71828…` 对应"加 `1 = log(e)`"；
  - **procession-normalization**（7005–7010，7034–7039）：对 procession 中的若干 capsule，"normalize by
    taking the **average**, over the various capsules under consideration"。
  即：原文的"procession 归一化"**就是取平均**，平均的对象是 procession 里的 capsule 标签。
- **〔已核〕(xi-d)**，txt 11022：`[suitably normalized, with respect to j ∈ |F_l|] log-volume`——
  索引写的是 **`|F_l|`**（集合），而 Step (x) 写的是 **`F_l^⋆`**（群，"where the average is taken over
  `j ∈ F_l^⋆`"）。
- **〔推断，非原文陈述〕** 这两处**很可能指同一个归一化**：`|F_l|` 是标签集，`F_l^⋆` 是作用在标签上的对称群
  （10917–10922 明说这些平均来自 `F_l^⋆` 在 theta 值标签上的作用），而 7005–7010 的 procession 归一化正是
  对这些标签取平均。但原文**没有**明说 `|F_l|` 索引与 procession 平均是同一个约定——这条识别必须由证明
  或显式约定补上，不能默认。
- **〔已核〕Prop 3.9(iii)**，txt 7080–7090：全局 log-volume 等于由 `J` 决定的 arithmetic line bundle 的
  degree，但仅「relative to a **suitable normalization**」；Remark 3.1.1(ii) 的权重公式与 7000–7010 的
  packet/procession 归一化都是候选，原文没有指认是哪一个。
- **要补的证明**（三条，按难度）：
  1. **把 (xi-d) 的 `|F_l|` 归一化识别为 procession 归一化**（即"对标签取平均"，7005–7010），从而不是
     一个未指定的"合适约定"——这是 `vQ = q₀` 有确定含义的前提。这里要的是**定义对齐**，不是新的估计；
  2. 证明 Prop 3.9(iii) 的"suitable normalization"是 packet 归一化 + procession 平均的组合（给出公式并对齐）；
  3. 在 1、2 之后，才谈得上"同一对象的 native 读数 = 输出读数"这类陈述。

## 玩具能说什么、不能说什么

`candidates/core-transport/DivideBackLaw.lean`（待修至可编译；见 W3）只做 M-i 的**形状**：

- 若读数是主单位上的对数，则"`M` 次幂的读数 = `M` × 读数"是可证定理，于是"除回"就是**除以标量 `M`**，
  不需要另设一个映射；
- 同一 `x = 4`、`M = 2` 处，范数读数**不**具备该性质（`‖4²‖/2 = 1/2 ≠ 1 = ‖4‖`），所以"除以 `M`"不是
  无内容的一步，性质也不是任意读数都自动成立。

它**不**说：`M` 的取值（M-ii）；(Ob4-1)/(Ob4-2)/(Ob4-3) 的 tensor-power Frobenioid 上的除回映射；
twist 不定性的行为；以及 M-iii 的任何一条。`ℚ_[3]` 是完备离散值域，`x ↦ x^M` 不是 `det^{⊗M}`。

## 对齐义务：IUT II 已取得，`0 ↔ ⟨F_l^⋆⟩` 的认同确实存在

先前记为阻塞的那条引文，已在取到 IUT II 后核实。**来源与取证**：

| 项 | 值 |
|---|---|
| URL | `https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf` |
| PDF SHA256 | `180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c`（1,203,855 B，`%PDF-` 头） |
| 页面标题页版本 | "December 2020"（首页文本：`INTER-UNIVERSAL TEICHMÜLLER THEORY II: HODGE-ARAKELOV-THEORETIC EVALUATION`） |
| 页数 | 174 |
| 文本化 `.txt` SHA256 | `7d5b7bd7d4e53c4d96b1ed24a05dffa1f9a5fae539b1129a9a12f0b7665e7fab`（479,196 B，分页标记 `===== PDF PAGE n =====`，与 I/III/IV 同格式） |
| 文本化方式 | `pypdf 6.21.2`（`research/round2-source-cache/extract_iut2.py`）；抽取时有 fontTools 缺失的告警，属 CFF Type1 字体编码，不影响正文可读性 |

**〔已核〕IUT II Corollary 4.10, (i)**，txt 7003–7010（PDF 第 158–159 页）：

> "(i) (Constant Prime-Strips) … Then, for each `t ∈ LabCusp^±(†D≻)`, the collection of data
> `Ψcns(†F≻)_t` determines, in a natural way, an F-prime-strip … **Let us identify the collections of
> data `Ψcns(†F≻)_0` and `Ψcns(†F≻)_{⟨F_l^⋆⟩}`** via the isomorphism of the second display of
> Corollary 4.6, (iii), and denote by `†F⊩_△ = (†C⊩_△, Prime(†C⊩_△) ≅ V, †F⊣_△, {†ρ_△,v}_{v∈V})`
> the resulting F⊩-prime-strip …"

即：IUT III 10922–10924 所指的那处认同（符号"`△`"由把 **`0`** 与 **`⟨F_l^⋆⟩`** 认同而来）**确实存在**，
且它把"标签 `0`"与"群 `F_l^⋆` 生成的那份数据"等同起来。

**这对第 1 条义务意味着什么**（区分已确立与仍属推断）：

- **已确立**：标签集里确实有 `0 ≡ ⟨F_l^⋆⟩` 这一认同；因此"对 `j ∈ F_l^⋆` 取平均"与"按标签（含 0）索引"在
  **标签层面是同一套索引**，不是两套互不相干的约定。
- **仍属推断**：(xi-d) 的 `[suitably normalized, with respect to j ∈ |F_l|]` 并**没有明写**它采用的就是这个
  认同下的 procession 归一化。所以义务从"取一个缺失的约定"降级为"**引用 Cor 4.10(i) 的认同，把 (xi-d) 的
  `|F_l|` 索引对齐到 procession 归一化**"——一条**定义对齐**，其依据现在在手上（II 7010 + III 7005–7010）。
- **未解决**：`coricity`/`Θ-link` 层面的同构类问题与本条无关；本条只谈归一化的索引。

先前"必须下载 IUT II 才能推进"的判断成立；**未**把这条对齐当成已证命题写进任何 Lean 文件。

## 结论

这三条是 H3 的**前置**，不是可选项：只要它们没被证明，(Ob4) 的"无害"与 (xi-d) 的"精确 log-volume"之间的桥
就只有文字、没有对象。**核心 GAP 保持 OPEN**；本文件不构成对任何 IUT 主张的支持或反驳。

本轮新增的一条实质结论：原文**并非没有归一化**——它写出的那条是 **procession-normalized（对 `j ∈ F_l^⋆`
取平均）**，且明说该体积对 (Ind1)(Ind2) 不变、把 (Ind3) 化为**上界不等式**（10904–10922）。这说明原文的
"coarse 读数"本身就是一种**平均意义上的读数**，而不是某个被指定的单点值。于是 (xi-d) 的
`[suitably normalized, w.r.t. j ∈ |F_l|]` 所缺的不是"随便一个约定"，而是**与这个平均的相容性证明**——
这正是上面的第 1 条义务。
