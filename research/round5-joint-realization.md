# 第五轮：同一 seed–κ–σ 路径的联合实现审计

日期：2026-10-20（Asia/Shanghai）。**全文状态：未形式化候选与来源阅读记录；没有新增已认证数学结论。** 本文独立于 Lean 验收，不能把其中的范畴论论证、候选判据或原文定理直接加入 fact-tree。G03、RI-01–08 均保持 open；第三、四轮合计 57 个已验收结果是模型或基域局部接口，不是 IUT 实现，更不构成 IUT／abc 的解决。

## 本轮最有信息量的候选精化

**应检查的是“带已选 κ 与 seed 的允许输出表示能否沿 σ 运输”，不能把它升级为“σ 必须固定 κ 代表”，也不能用未带这些数据的 fullness 宣称它已经成立。**

IUT II Example 1.7 的 fullness 比“存在某个对象上的某个 lift”强：若已经固定 radial object r，并且 a 是 Φ(r) 的自同构，则 fullness 直接提供 r 的某个自同构 h，满足 Φ(h)=a。真正尚未闭合的是：r 的原定义是否已经包括所选 κ **代表**、seed-region、splitting action 与输出实现；若只包括 poly-isomorphism／orbit，h 可能只保持整个 orbit。

另一方面，RI-05 允许新的 admissible choice c′。因此固定**起始** κ 后沿允许 arrow 到 c′，已经足以构成同一条路径；并不需要 c′=c，也不需要 κ′=κ。若 Thm.3.11(i) 的 Ind1 确实在整个输出数据 (a),(b),(c) 及其 region 实现上给出这样的运输，便可以直接在 coric 端后复合，不必另外提升成原 holomorphic theater 的自同构。这是值得优先尝试的较弱出口。

另一个可用的新切口来自 III Remark 3.11.4(i), pp.171–172：其相关数据只在乘以 roots of unity 的 orbit 层次使用。故先要求某个任意选定 θ 代表被严格保持，可能加入原文没有要求的刚性；先运输 θ 的 torsion orbit／生成理想，再选择允许代表，是更贴近来源的候选路线。它仍须证明实际有限域、region 与坐标相容，不能据此直接关闭 RI-03–05。

## 1. 固定来源、版本与本轮实际阅读范围

本轮复用已有缓存，没有新增下载，没有运行来源中的程序。对两个 PDF 的 SHA256 重新计算，与既有登记一致；本轮实读的是缓存全文提取文本，没有重新做 PDF 视觉核验，也没有重建全部引用证明。

| 来源 | 官方 URL、版本、固定字节 | 本轮实际读取 |
|---|---|---|
| IUT II | [作者官方 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)，December 2020，174 页；`round3-source-cache/iut-II-official-retrieved-2026-10-16.pdf`；SHA256 `180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c` | Example 1.7 与 Remark 1.7.1，pp.32–35；Example 1.8(i)–(v)，pp.35–40，并读 p.40 的 (vi)–(viii) 开头；Cor.4.6(i)–(v)，pp.137–139；Definition 4.9(i)，p.154 |
| IUT III | [作者官方 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)，May 2020，199 页；`round2-source-cache/iut-III-official-retrieved-2026-10-16.pdf`；SHA256 `9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9` | Prop.3.1(i),(ii)，p.93；Prop.3.2，pp.98–99；Prop.3.4(ii)，pp.102–103；Prop.3.7(ii)–(v)、Def.3.8(i)，pp.110–112；Remark 3.9.5 的 (Ob5)，p.134；Thm.3.11，pp.153–159；Remark 3.11.3 后段及 Remark 3.11.4，pp.170–173；Cor.3.12 声明、U 的定义、Fig.3.6 与证明 (i)–(vi) 的已读部分，pp.173–178 |

页码均是缓存预印本的印刷页码。URL 是已登记原始下载地址，本轮没有断言远端目前仍为同一字节。先读的工程背景为 `round3-semantic-audit.md`、`round3-realization-obligations.md`、`round2-source-audit.md`；IUT I 的 procession 定义本轮没有重新逐页核验，使用其第二轮已登记定位，不能把本轮写成重新审完全部 IUT I。

## 2. Fullness 到底给了哪一种 lift

以下都是待形式化的范畴论候选分析。

### 2.1 固定 r 的 lift 已包含在 fullness 内

令 Φ:R→C 是 Example 1.7 中的 groupoid functor。若 Φ full，则对固定 r：

```text
Aut_R(r) → Aut_C(Φ(r))
```

满射。这里不用 essential surjectivity；后者用于先找到所需 coric object 的 radial 实现。若给定的对象仅通过 β:Φ(r)≃c 识别到 c，则先提升 β⁻¹aβ，再用 β 回到 c。

因此不能把问题简单描述成“fullness 无法固定 source object”。它能固定 r，甚至能令 source/target 都为 r；但 r 中究竟保留哪些数据，必须逐项读定义。

II Example 1.7(ii), p.33 的 tautological multiradialization 使用 `(R,C,α)`，其中 α 是 **full poly-isomorphism**。Example 1.8(iii),(iv), pp.38–39 使用 Γ-orbit／Ism-orbit 型的 poly-isomorphism。保持这些数据不等于保持 α 的某一指定单值代表。Definition 4.9(i), p.154 又明确将 ×μ-Kummer structure 定义为 Ism-orbit，并以所有 open H 的 lattice images 刻画。

### 2.2 固定 fiber 不是额外的自动满射定理

严格 fiber `Φ⁻¹(c)` 的 arrows 本身投影为 `id_c`，所以不能直接在该 fiber 内寻找投影为 σ≠id 的 arrow。要比较 σ 前后的 fiber，必须使用沿 σ 的运输，或采用带识别 β 的 homotopy fiber，并写出 β 的变化。

即使带 decorations 的遗忘函子具有“从固定 source 提升任意 base arrow”的性质，也只保证某个 target decoration；它不保证 target decoration 等于原 decoration。但若这个 target 正是 admissible c′，且输出映射等变，前一种性质便足够完成 G03 的单条路径。

一个用于防止量词偷换的未形式化小模型：取 R=C=B(C₂)、Φ=id，所以原 Φ full。让 C₂ 自由交换二元素集合 D={0,1}，把 decorations 组成 action groupoid E=D//C₂。E→B(C₂) 能从任意固定 d 提升任意群元素到移动后的 d′；非平凡元素却不能提升成固定 d 的自同构。这既说明“原 fullness ⇒ 固定 decoration 的 lift”无效，也说明“不能固定 decoration ⇒ 所有 c′ 路径失败”无效。此模型不是 IUT 反例。

## 3. 精确的新审计对象：联合数据上的三个方块

先固定实际初始数据、n、m、p、j=3。令 c 是一个**实际** Kummer choice，g∈Seed(c)。使用以下占位类型仅描述尚待实现的对象，不把性质作为公理导入：

```text
W_c                 holomorphic finite packet
P_c                 coric finite packet
κ_c : W_c ≃ P_c     chosen representative, with all-H data
S_c                 splitting monoid (with its torsion convention)
μ_c : S_c → End(P_c) its actual multiplicative action in this presentation
out(c) ⊆ P_c        actual region representation
```

沿 σ=(2 3) 的允许 joint arrow 应产生 c′、R_a:P_c≃P_c′ 和 τ_a:S_c≃S_c′。必要的检查分三层，不能用一个“natural”字样代替：

**K 方块（如采用重新选 Kummer 表示的路线）：**

```text
W_c  --κ_c-->  P_c
 | B_a          | R_a
 v              v
W_c′ --κ_c′--> P_c′

R_a ∘ κ_c = κ_c′ ∘ B_a.
```

B_a 必须是允许的 source-data arrow，不能随意定义成 κ_c′⁻¹R_aκ_c 后就声称其来源合法。如果走 coric 端直接后复合的路线，可不要求 B_a 存在；替代义务是：`(c,a)` 属于原文允许的输出表示，并且该表示的 region **确实**是 R_a(out(c))。这避免给 G03 添加不必要的 holomorphic lifting 条件。

**A 方块（splitting action）：**

```text
R_a(μ_c(s)(z)) = μ_c′(τ_a(s))(R_a(z)).
```

只有证明原表示允许这样运输 action，才能在模型中使用共轭式 `μ_c′(τ_a(s))=R_a μ_c(s) R_a⁻¹`。任意线性格自同构未必与原来的 field multiplication 交换，不能保持旧 action 的同时只移动一个点。III Thm.3.11(i)(b) 把 monoid 的 subset 与 multiplicative action 一起列为数据，因此这里有明确来源靶点。

**O 方块（region 与完整输出数据）：**

```text
Adm(c) ∧ Allowed(a,c)
  ⇒ ∃c′, Adm(c′) ∧ R_a(out(c)) ⊆ out(c′) ⊆ U_3.
```

仅为本轮固定 seed 证明 `R_a(κ_c(g))∈out(c′)` 即足够；没有必要先证明上式对所有 c、a 成立。但 Adm(c′) 必须涉及 (a),(b),(c) 的共同表示，而不是只涉及 packet (a)。III Cor.3.12 p.175 又讨论把 regions 解释为 F⊩▶-prime-strip；若采用该限制后的表示族，需要同时核实它不会排除当前 c′，不能仅引用 p.174 的 union 名称。

最后才接坐标方程：

```text
u=(b₁,b₁,b₂,b₁), v=u∘σ⁻¹=(b₁,b₁,b₁,b₂),
pr_v R_a = (⊗ᵢ ψ_i) σ_* pr_u.
```

这一次 ψ_i 必须来自该 a，不能事后从所有 A(k_v) 中任选。θ=q̂_(b₁)^9 的来源仍为 b₁。改变 slot 并不改变来源 place；stage j=3 也不会因为 slot 3 被交换而变成 stage 2。

## 4. 一个可执行的 kernel-orbit 检验，替代泛称“兼容”

这是未形式化候选判据，不是已经认证的 IUT 结构。

假设某一具体模型已实现 Φ:R→C full，并把完整 decorations 实现为 Aut_R(r) 作用的集合 D(r)。令 d∈D(r) 是已选 κ、seed-region、action 等的共同数据；设 a 是所需 coric 自同构，选一个 h₀∈Aut_R(r) 满足 Φ(h₀)=a。记

```text
K_r = ker(Aut_R(r) → Aut_C(Φ(r))).
```

那么同一 a 的其它 lifts 可写成 h₀k，k∈K_r。若所需 target decoration 是 d′，候选存在性判据为：

```text
∃h over a, h(d)=d′   ⇔   d′ ∈ h₀(K_r·d).
```

固定代表的强版本取 d′=d；G03 的弱版本取**所有实际允许目标** A⊆D(r)，检查：

```text
h₀(K_r·d) ∩ A ≠ ∅.
```

这里 A 不能仅由“使结论成立”的坐标等式定义；它应先从原文 admissibility、region 与完整 (a),(b),(c) 数据给出，再把坐标条件作为额外核验。换一个 h₀ 应给相同的候选集合，这是该判据下一步可独立验证的模型命题。

这也提供明确的**条件式否定出口**：若能从原来源导出一个 K_r 不变量 J，并证明 J(d′) 对所有 admissible targets d′ 的取值均不同于 J(h₀d)，则该具体起始 witness 的 σ 路径不存在。单个 h₀ 不兼容、单个严格代表失败或只发现一个不同 κ 的 lift，均不够。

最先值得尝试的 J 是所有 open-H lattice image 的族以及 action 的局部 support 数据。II Def.4.9(i) 给前者一个比“基域格相同”强得多的来源。需注意：σ 自然把 slot/place support 一起搬动；若目标允许这种搬动，support 不构成 obstruction。只有从原定义证明某个 support 必须固定，且 σ 不能满足，才得到否定条件。不能自行冻结 slot j 来排除已被 Ind1 允许的置换。

## 5. 可减少刚性的新切口：先审计 torsion orbit，再选 θ

III Prop.3.4(ii), pp.102–103 在指定 j-slot 的 partial packet 中构造 LGP-monoids；Prop.3.7(ii),(v), pp.110–112 明确给 local fractional ideals 作为 subsets/submodules，并从 monoid 元素生成这些 ideals；Def.3.8(i) 的 Θ-pilot 由 generators up to torsion 决定。这些是 seed-region 的实际来源，比单纯“有一个抽象 pilot object”更具体，但仍没有在本工程实现指定 tuple 的纯张量 membership。

III Remark 3.11.4(i), p.171 明确在相应 log-Kummer correspondence 中采用 roots-of-unity orbits，而不是 orbit 中的指定元素；pp.171–172 解释其对 theta values 与 Frobenioids 的影响。于是可将 RI-03 的优先目标改写为下列**候选研究步骤**，而不是立即强求固定 θ：

1. 在实际 partial packet 中实现原 fractional ideal J(c)，证明所需 torsion orbit 的至少一个代表生成 J(c)。
2. 将这个 ideal／orbit 与实际 κ 的输出 region 连在同一 c 内。
3. 运输完整 ideal／orbit、splitting action 以及其 embedding，证明它们给 admissible c′。
4. 最后在该已建立的路径中选择一个代表 θ′，证明 θ′ 属于所需有限域，且其局部估值、非零性与坐标公式满足目标。

若 θ′=ζθ，不能擅自假定 ζ 已在原有限完成域内；应证明所属域或显式扩域并重审 lattice／invariants。也不能把 root-of-unity multiplication 与任意 χ、ψ 交换。可尝试在源端把 θ′ 作为输入重新应用逐元素的粗估值界，而不是要求 χ(ζθ)=ζχ(θ)。这些仍是待证明接口。

Thm.3.11(iii)(c),(d), pp.158–159 已对 evaluation maps 陈述 up-to-indeterminacy 的兼容性，所以不能声称原文完全没有评价相容性。另一方面，Remark 3.11.4(iii), p.173 特别把几何 containers 在 evaluation **之前**不受 Ind1/2 影响，与评价后的数据区分。我们仍需要把其作用域落实为上述 A/O 方块；“container 不变”本身不能替代评价后指定纯张量的运输公式。

## 6. 下一步只做一条小而真实的源数据连接

### 6.1 后续核对揭示的限制：后复合不等于新的 Kummer isomorphism

III Fig.3.6, p.176 将两层区别列得很清楚：local LGP-monoids／copies of F_mod 需要 mono-analytic containers，其 Kummer theory 与 Ind1/Ind2 不兼容；étale theta function、mono-theta environments／κ-coric geometric structures 的那一层独立于这些 containers，并有相应兼容性。Cor.3.12 proof (vi), pp.177–178 又把 splitting 及 log-link 相容性的来源追到 Galois evaluation 和 conjugate synchronization。

所以，直接后复合路线**没有**证明 `R_a∘κ_c` 本身属于原“relevant Kummer isomorphisms”。应保留两阶段类型：

```text
ActualKummerChoice c
ActualInd1OutputChange a over the output of c
RepresentedRegion(c,a)
```

然后证明 `RepresentedRegion(c,a)=R_a(RepresentedRegion(c,id))`（或对所需元素的单侧 membership），再证明 `RepresentedRegion(c,a)` 是 p.174 中原 possible images 的成员。只有有额外来源定理时，才能把 `(c,a)` 合并记成一个新 Kummer choice。它省去了不必要的严格固定 κ 与 holomorphic lift，**没有省去 RI-05 的真实表示族识别**。

这也精化了第三轮“同一个 κ 与 σ 联合提升”的措辞：本轮要求的是**同一联合源数据 witness 出发的连续允许路径**；动作后 κ 代表数值不变不是要求。旧报告不作改写；上述精化不撤销其中对 joint admissibility 的要求。

### 6.2 一个现在可以逐项核对的同步方块

II Cor.4.6(iii), p.138 不只是说有若干局部 Kummer maps：它明确规定每个 v 的 Π_v-conjugacy indeterminacy **independent of label t**，并与 symmetrizing isomorphisms 相容。其 (iv),(v), pp.138–139 再把 local evaluation、global Frobenioid maps 与这些局部 maps 连起来。这给出了之前“同步数据”一词的一条具体量词。

若 f_t 是同一 collection 中标签 t 的 Kummer map，s^hol_(t,t′)、s^cor_(t,t′) 是来源的 symmetrizing maps，待实现的同步方块形如：

```text
f_t′ ∘ s^hol_(t,t′) = s^cor_(t,t′) ∘ f_t
```

等号须按原 conjugacy／poly-map 语义表达；不能为不同 t 任取互不兼容的 conjugator 来强行制造等号。这不是要求每个可容许 κ 代表在所有 label 下 literally 相等，也不是要求所有 Ind2 独立作用在后续输出中变成同一个作用：它限制的是构造**起始 Kummer collection**时的共同来源。

指定 σ 的来源是 procession automorphism，并不自动就是这里的 F⋊± symmetrizing map。可操作的顺序是：先在该同步方块内建立起始 seed–κ，再从 Thm.3.11(i) 的输出 indeterminacy 运用 σ；不要直接用 Cor.4.6(iii) 宣称任意 σ 已有同步的 holomorphic lift。

torsion-orbit 路线亦保留这条限制。它只消除无必要的单个 θ 代表刚性，不自动消除 labels 间 conjugacy 的一致性、理想到具体 region 的实现或原 U 的 membership。

### 6.3 最小交付目标

优先试验固定 m、固定 κ、Ind2 取实际恒等代表，不调用 Ind3。从 Thm.3.11(i) 的 procession functor 出发，直接构造 σ 对完整输出 (a),(b),(c) 的代表变化，取来自 Prop.3.7(v) 的一个实际 fractional ideal。目标是证明：

```text
this particular represented ideal after σ
is one of the regions used in the original Cor.3.12 union.
```

若可以直接完成，再选 seed 并核验 projection 公式；不必先证明 κ 的严格稳定子满射。若直接后复合路线不能完成，则把失败记录为 O 方块中具体的 admissibility／action 条件，再使用 §4 的 kernel-orbit 判据，区分“换 lift 可修正”“仅换代表可修正”“所有允许 target 均失败”。

固定 m 仅用于选取 union 的一个候选成员；它不是对全局 Cor.3.12 证明中 Ind3 的删除。该证明 (iii)–(v), pp.176–177 明确讨论跨列 unit/value data 的联合处理以及 vertical shift 所需的 upper-semi-compatibility。

本轮没有构造真实 c′，没有证明上述交集非空或为空，也没有证明实际 pure tensor 的 seed membership。本轮提出待形式化检验的审计假设：**需要重点核查数据层级与输出相容性；固定 κ 代表的稳定性可能是过强要求。** 这不是经过 Lean 认证的数学结论。所有 gap 继续 open。
