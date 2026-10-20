# 第二轮来源审计：G03 的 membership / transport 桥梁

检索日期：2026-10-16，Asia/Shanghai。范围：Urahigashi 固定 GitHub tag v0.8.0 的独立短文，以及其直接引用的原 IUT I/III/IV 段落。数学状态：**本报告未提供 Lean 证明；所有公式解释、候选反驳和修补条件均是待检验的研究主张。** “原文明确”只表示已经找到相应文字或公式，不表示该原文定理已由本项目认证。

## 1. 本轮推进到了哪里

已经把 G03 缩小为可逐项审计的来源桥梁：

- 原 IUT 的 procession 定义确实容许每一 stage 的 capsule-full poly-morphism；原文的 Ind1 确实指向 procession 的自同构，不能简单以“原理论没有标签置换”否定异议。
- 原 IUT IV Step (v) 确实先固定 tuple、取 i†=j 和该位置的 q 参数，再用一个固定 packet 上的线性自同构 φ 估计，声称其任意性吸收 Ind1/Ind2。
- 异议作者从这些原文构造一个跨 tuple 的置换像。尚待形式化的是该像与**实际** Θ-pilot 可能像之并的精确对应，以及全部 Kummer/Ism 坐标兼容性。
- 因而本轮不能宣布“异议已证”，也不能宣布“已反驳异议”。可以明确列出真实 IUT 内容必须补齐的定理。

## 2. 固定文献与阅读范围

| 来源 | 本轮实际读取的范围 | 版本与页码 |
|---|---|---|
| Urahigashi | 完整 TeX §1–5；重点 PDF pp.1,4–6；视觉核对 p.5 的 Lemma 4 和目标 tuple | 固定 tag v0.8.0；论文 README 标 Version 1.0.0；Draft 2026-10-05；6 页 |
| IUT I | §0 p.34；Definition 4.1(iii),(iv) p.96；Definition 4.10 pp.119–120；pp.120–121；Proposition 6.9 p.169 | 官方 PDF 首面 May 2020；186 页 |
| IUT III | pp.10–11,32,36,93,97–99,102–103,112,127–128,153–156,173–175 | 官方 PDF 首面 May 2020；199 页 |
| IUT IV | pp.9–10,13,27–28；视觉核对 p.27 中 i†、λ、Ind1/Ind2 的段落 | 官方 PDF 首面 April 2020；87 页 |

官方 PDF 的下载 URL 可能以后改变；本轮已用本地缓存和 SHA256 固定其实际字节。页码是预印本印刷页码；这几个文件的 PDF 页序与印刷页码一致，**不是** 2021 期刊连续页码。完整哈希、来源 URL、派生文本及阅读标记见同目录 round2-sources.json。没有执行下载仓库内的代码。

主要来源：

- [Urahigashi 固定 tag 原稿](https://raw.githubusercontent.com/turahigashi/iut-explicit-initial-theta/v0.8.0/stepv-local-noncontainment/paper/stepv_local_noncontainment.tex)
- [IUT I 官方 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf)
- [IUT III 官方 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)
- [IUT IV 官方 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf)

## 3. 固定类型、对象与三个不同的“位置”

以下符号表是对作者模型的有类型重述，仍需要证明它实现原 IUT 的定义。

令 E 为 F_mod 在 p 上方的 places，J={0,…,j}。对 v∈E：

- k_v=K_underline(v) 是一个完成域；
- q̂_v 是原 Tate 参数的 2ℓ 次根，ρ(v)=ord_p(q̂_v)；
- I_v=p⁻¹ log_p(O_v^×)（本例 p 为奇素数）是 log-shell；
- A(k_v) 是保 log_p(O_v^×) 的 Q_p 线性自同构群；它是短文选用的较大允许容器，不应直接定义为真实 Ism。

模型中的 packet：

```text
P_j = ⊗_(i∈J) (⊕_(v∈E) k_v)
    ≅ ⊕_(v⃗∈E^J) k_(v⃗)

k_(v⃗) = ⊗_(i∈J) k_(v_i)
pr_(v⃗) : P_j → k_(v⃗)
```

需要一直分开：

1. **stage index j**：决定 capsule 大小 j+1 及 theta 的指数 j²；
2. **tensor slot i∈J**：在一次允许的置换后改变；
3. **place v_i**：跟随被搬动的那个因子，不会因为 slot 改名就变成另一 place。

对 σ∈Sym(J)，短文使用：

```text
w⃗ = v⃗ ∘ σ⁻¹
σ_* : k_(v⃗) → k_(w⃗)
σ_*(⊗_i z_i) = ⊗_i z_(σ⁻¹(i))

pr_(w⃗) ∘ R_(σ,ψ)
    = (⊗_i ψ_i) ∘ σ_* ∘ pr_(v⃗)
ψ_i ∈ A(k_(w_i))
```

最关键的具体追踪（j=3，σ=(2 3)）：

| slot | 原 tuple u⃗ 的 place | 原元素 x 的分量 | 置换后 slot | 目标 tuple v⃗ 的 place |
|---|---|---|---|---|
| 0 | b₁ | 1 | 0 | b₁ |
| 1 | b₁ | 1 | 1 | b₁ |
| 2 | b₂ | 1 | 3 | b₂ |
| 3 | b₁ | θ=q̂_(b₁)^9 | 2 | b₁ |

于是作者的目标像为 y=1⊗1⊗θ⊗1，落在 k_(b₁)⊗k_(b₁)⊗k_(b₁)⊗k_(b₂)。**θ 的来源仍是 b₁；目标 slot 3 此时是 b₂。** 这是短文需要在真实 IUT 中实现的对应，不是单纯把 q_(b₁) 与 q_(b₂) 识别。

## 4. Lemma 3（membership）的逐桥梁审计

固定原稿：§4，PDF pp.4–5；TeX 标签 l:member（缓存行 282 起）。

| 桥梁 | 原文明确提供了什么 | 短文额外完成的解释／仍需证明 |
|---|---|---|
| M1 theta 来源 | IUT III p.11 把 splitting-monoid generators 与 q̂_v 的 j² 次幂联系 | 在具体有限完成域内构造 θ，连同 root-of-unity、field-of-definition 与估值证明 |
| M2 单 slot 嵌入 | III Prop.3.1(ii) p.93 明写其它因子 tensor with 1；Prop.3.4(ii) pp.102–103 指定 j-slot、v-summand 的 partial packet 及乘法作用 | 分配有限 invariant subspace 的坐标，把该嵌入展开为完整 tuple 中的纯张量 |
| M3 pilot 到 region | III Prop.3.7(v)、Def.3.8(i) p.112 通过局部分式理想及 splitting generators 构造 Θ-pilot | 证明该抽象 pilot 的这一个具体 region 确实包含作者所取 g；不能只把“对象由理想确定”默认为已给出某一 subset |
| M4 Kummer 到 mono-analytic packet | III Thm.3.11(ii)(a),(b) p.155 给 packet 与 splitting monoid 的 Kummer isomorphisms；Prop.3.2 pp.98–99 给对应 poly-isomorphisms | 为同一个选择构造 κ，证明它在原来的 v⃗-summand 上分解为保 log-shell 的逐因子线性映射 χ；须处理 Galois invariants、Q-span 与 Q_p 结构 |
| M5 进入 U_j | III Cor.3.12 pp.173–174 定义 relevant Kummer isomorphisms、Ind1/2/3 下的 possible images 之并 | 证明 M3/M4 的选择属于这个 **同一个** admissible family，得到 pr_(v⃗)(X)=χ(x) 而非仅抽象同构 |

M4 所引用的 Ism compatibility 在 III Prop.1.2(vi) p.32 有实质依据：局部模块同构兼容 Galois action、log-shell 和 log-volume。但从 ind-topological module 的表述到作者的固定有限域坐标，需要写出限制/取不变量的定理。它不是“任意环同构”，也不能假设会保留每个元素的 valuation。

可支持 IUT 的具体反驳条件：

- 找出 M3 的真实 image-region 定义，使该纯张量 g 不在相应 region，并证明这种排除同时兼容原文的分式理想构造；
- 或证明 M4 的有限坐标表达不是作者写出的 χ，指出准确的混合、子空间限制或标量归一化，并重新计算；
- 或证明 M5 的 Kummer choices 不能与后续置换同时属于一个允许族。

单说“需要区分不同 ring structures”或“Ism 小于 A(k)”尚不能反驳：短文对 A(k) 的使用旨在证明对更大群中的每个 ψ 都不能包含；真正有效的反驳要指出**实际像不在这个过度近似族中**，或者种子根本不是允许输入。

## 5. Lemma 4（transport）的逐桥梁审计

固定原稿：§4，PDF p.5；TeX 标签 l:transport（缓存行 320 起）。

| 桥梁 | 原文根据 | 审计结果及剩余义务 |
|---|---|---|
| T1 stage 自同构 | IUT I Def.4.10 pp.119–120；§0 p.34 | 文字确实给每 stage 的 capsule-full poly-morphism，没有额外列出跨 stage 的自然性方程。固定 j-stage 的 σ、其它 stage 恒等是有直接来源根据的构造 |
| T2 属于 Ind1 | III Thm.3.11(i) p.154 | Ind1 明指 procession automorphisms；III p.10 的导言也明说这些 index sets 接受任意置换。σ=(2 3) 固定 0，不必使用有争议的 core-label 搬动 |
| T3 place 与 slot | I Def.4.1(iv) p.96；III Prop.3.2 pp.97–99 | prime-strip morphisms 按 place 索引；slot 可置换，但同一被搬因子内的 place 仍保持。需正式构造分配律同构，并证明 projection 方程 |
| T4 Ind2 后的形式 | III Thm.3.11(i) p.154；Prop.1.2(vi) p.32 | 原文按每个 factor 的每个 place-summand 给独立 Ism。仍需证明其有限坐标作用落在作者 A(k) 中，以及复合公式 R_(σ,ψ) |
| T5 U_j 对复合封闭 | III Cor.3.12 pp.173–174 的 possible-images union | 原文未在这些页把 admissible family 写成一个可执行 action/orbit 定义。短文把“受不定性影响”展开为：先选像，再任意 Ind1，再 Ind2 后仍是像。这是需要认证的核心闭包定理 |

T1/T2 是这次源审计中对异议最直接的支持；T3–T5 是把纸面对应升级成真实 IUT 定理最需要精确化的部分。特别要同时运输 Theorem 3.11 的整个 (a),(b),(c) 数据与 action，而不是只搬动一个点后留住所有其它数据；需要以一个联合等变性定理证明短文所用的坐标方程。

候选反驳也必须落在这个层次：例如给出 admissibility 谓词，证明该 σ 与 κ 的复合不在允许族，并说明为何这不违背原文 Ind1 的 procession-automorphism 定义。不能仅因 σ 不来自原 Hodge theater 的某个自同构就排除它；Ind1 的定义来源是更弱的 procession 数据。

## 6. 固定 tuple 上的 φ 与跨 tuple 置换的差别

原 IUT IV Prop.1.2 p.10：

```text
L_(v⃗) = ⊗_i log_p(O_(k_vi)^×)
φ : L_(v⃗) ⊗ Q_p ≃ L_(v⃗) ⊗ Q_p
φ(L_(v⃗)) = L_(v⃗)
```

Prop.1.4(iii) p.13 给 φ(p^λ·R̃_(v⃗)) 的上界。Step(v) pp.27–28 固定 v⃗ 后取 i†=j、λ=j²ρ(v_j)，并说 φ 的任意性考虑了 Ind1/Ind2。

异议中的 σ_* 起初却是：

```text
k_(u⃗) → k_(v⃗),   u⃗ ≠ v⃗
```

两侧抽象同构不等于输入的 θ 来源已变成目标 v_j。若把 σ_* 和其逆结合成固定 k_(v⃗) 的自同构，必须把输入理想也同步送过来；不能保留目标 λ=j²ρ(v_j) 而遗忘输入仍来自其它 slot。**待证的正是这一同步在原理论中如何完成。**

原文 p.28 随后对 i† 对称化并取 weighted averages。这解释了为何最终数值表达是对称的，但不能直接替代“先对全部可能像取并，再取 hull”的局部包含证明。候选正式检查应明确区分：

```text
sup_(σ) localSize(σ ⋅ region)
average_(σ) localSize(σ ⋅ region)
average_(v⃗) sup_(σ) localSize(σ ⋅ region)
```

置换不改变 tuple 的乘积权重，并不足以把最后一个式子自动变成单一代表的平均。这里是建议检验的分析结构，不是本轮已证不等式。

## 7. 积分结构、M_(v⃗) 与 hull 的精确位置

必须区分四个积分结构：

1. 原 holomorphic packet 的环整数结构 O（III Prop.3.1(ii)）；
2. mono-analytic log-shell 的 tensor lattice I（III Prop.3.2(ii)）；
3. IV 的 L=⊗ log_p(O_i^×)，它与 I 差显式 p 的幂；
4. R̃=normalization(⊗ O_i)，用来定义 fractional-ideal hull 及局部体积归一化。

短文把最后估计容器写为：

```text
M_(v⃗) = p^(floor(λ-d_I-a_I)-b_I) R̃_(v⃗).
```

它由 III Remark 3.9.5(i) p.127 的 hull 定义获得候选后果：hull 是包含 U 的最小 λ₀·O 型区域，或在非 relatively compact 情况下为整个 packet。要把任一像 y 推到 p²R̃⊆pr(hull U)，仍需证明该坐标实现下的 O 正是 R̃、投影确实给一个 R̃-module，以及每个 simple-field component 的 valuation 解释一致。

本例的源数据声称 e=(105,105,105,35)，d_I=138/35。使用 IV Prop.1.2 的 small-ramification 分支，候选有限算术为：

```text
a_I=2/35, b_I=-2/35, λ=54/7
floor(λ-d_I-a_I)-b_I = 107/35 > 2
```

短文自身使用较松的 μlog(M)≤-(97/35)log p，与候选 hull 下界 -2 log p 冲突。上述纯有理数计算可以优先交 Lean 检验，但它只认证“这些输入和结构前提一旦成立后的算术”，不能取代 M1–M5、T1–T5。

## 8. 支持 IUT 的可操作修补方案

### R1：证明源追踪相容性，保住原估计

完整定义 q-source、stage-label、active tensor slot，以及 κ/Ind1/Ind2 的 action。证明：

```text
every admitted output in the fixed tuple v⃗
is controlled by the source ideal with λ = j²ρ(v_j).
```

若能证明，该定理直接排除短文所需的某个 membership/transport 前提；必须指出具体被排除路径。不得把这个结论直接放进 structure 字段或 axiom 当成“修补”。

### R2：允许置换，改成来源最坏值的容器

若短文的轨道模型忠实，候选修改是追踪所有 σ⁻¹(j) 的来源，对固定 tuple 选择：

```text
λ_orbit(v⃗) = min_(allowed σ) j² ρ(v_(σ⁻¹(j))).
```

固定 0 的置换只需对非零 slots 取允许的来源；若实际群更小，则只取实际 orbit。本例会把 λ 从 54/7 降为 9/7；相应容器变大，已不能用同一元素反驳该修改版界。

这只是一个**候选局部补救**。必须重新证明包含、hull 上界和最终全局估计。通常将负贡献换成 orbit 最坏值会削弱高度控制；尚未证明仍能导出 abc。

### R3：在全局层面证明真正的置换不变估计

保持局部容器的来源依赖，直接对完整 orbit/hull 求全局 bound，而不是把每个代表的 bound 事后平均。可尝试 groupoid-indexed sum、transport of measure、orbit decomposition。需要证明取并导致的 enlargement 仍在原误差预算以内。

### R4：缩小或改变允许像族

若补充几何相容性排除了该路径，须重新证明 multiradiality、coricity、Ind1 定义和 Cor.3.12 的目标覆盖仍成立。仅删掉导致困难的置换会改变理论，不能算原理论已被验证。

## 9. 给形式化工作的最小真实接口

建议分两层，且不能混淆认证状态：

- 模型层：有限标签、tuple 置换、source-place 追踪、矩阵或模块 action、轨道并及容器比较。
- 实现层：真实 IUT 的 pilot-region、κ、Ind1/2/3、log-shell、normalization、hull 到模型的 map，并证明 M1–M5、T1–T5。

预期接口示意（不是本轮已经实现的 Lean 代码）：

```text
Realization
  packetCoordinates
  pilotRegion
  kummerChoice
  admissibleChoice
  concreteInd1Action
  concreteInd2Action

Required theorems
  seed_mem_pilotRegion
  kummer_coordinate_formula
  permutation_is_admissible
  projection_transport_formula
  possibleImages_closed_under_composition
  source_parameter_tracking
  hull_integral_structure_compatibility
```

在这些真实接口没有建立以前，G03 必须保持 open。局部 non-containment 即便将来认证，也不自动证明 Cor.3.12 错误、Theorem 1.10 的最终全局不等式错误或 abc 的否定。短文自身没有提出这些更强结论。

## 10. 剩余阅读与验证义务

- 尚未核验完整初始 Θ-data 的全局构造；本轮重点是 §4 来源接口。
- 尚未逐行重建 IUT II 引用链，以及 [AbsTopIII] 的 module/Galois reconstruction；这影响 M4。
- 尚未给原“possible images”独立的、完全显式的 Lean admissibility 定义；这影响 M5/T5。
- 尚未证明 R1、R2、R3、R4 中任何一种方案。
- 视觉核对仅用于辨认公式、脚注和相邻文字；不等于定理验证。没有使用下载内容的可执行代码。

