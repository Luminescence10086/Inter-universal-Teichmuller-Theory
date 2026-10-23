# H1–H3 设计稿：从原文闭环倒推联合见证的最小类型

日期：2026-10-23。状态：**设计，未形式化，未入 fact-tree**。依据 `research/core-compatibility-2026-10-23/`
（README 与 source-analysis），并等待 M1–M4 的静态清单回填引用。本文件不声称 J 已存在、不声称原文等于本模型、
不关闭核心 GAP。

## 0. 目标与边界

目标是给 III Thm 3.11 → Cor 3.12 的核心比较一条**可以逐项检验**的路径：固定的合法初始数据 D、native q
读数 q₀ = −|log q|、上界 B。要证的是 q₀ ≤ B（G0）。箭头是研究依赖方向，不是已证依赖边。

三类错误先钉死，后面每条设计都照此检查：

1. **把结论塞进类型。** `V_native = q₀` 或 `V_out ≤ B` 不能作字段；它们只能是定理。
2. **从 hull 反推原区域。** `InHullOfImage` 只是"输出落入 hull"的一个方向；`V(E) ≤ V(Hull E)` 不能倒推
   原输出有 hull 的体积。
3. **用标量相等冒充来源相等。** iQ5 之后只剩数值；相同数值不能反推同一 prime-strip 见证。

## 0′. 接收核对（主线抽查，非采信自述）

| 被核对象 | 主线实际做了什么 | 结果 |
|---|---|---|
| M1 的图定位 | 读 txt 9237–9264 原文 | 两行四节点、`∼→` 横箭、`↑⏐` 竖箭确实存在于文本，M1 未凭空构造 |
| M1 的 IPL 引述 | 读 txt 9861–9878 | 与 M1 引述**逐字相符**，且原文确为 `linking isomorphisms of "intermediate" prime-strips are given by composing …`（族索引） |
| M2 的 (Ob4) 定性 | 读 txt 8135–8144 | 原文确实是"does not result in any substantive problems such as … an indeterminacy arising from confusion between … line bundle and its M-th tensor power" —— **断言**，无界、无不变性证明 |
| M2 的 (xi-d) 归一化 | 读 txt 11014–11027 | `[suitably normalized, with respect to j ∈ |F_l|]` 确实存在且**无公式** |
| M4 的声明定位 | 在 `external/iut` 内 grep 四条 | `OrbitObj`(43)、`OrbitHom`(52)、`ValBPS.valIso_subsingleton`(296)、`IsFrobenioid.pullback_surj`(**251，结构字段**)、`degree_hom`(305)、`degree_frobenius`(328) 全部命中 |
| M1 的 CSV | 独立解析 | 28 行 × 10 列、无空格、状态含 `STATIC_ONLY`/`PARTIAL`、交付哈希与磁盘一致 |
| M4 的 CSV | 独立解析 | 8 行 × 13 列、无错列、`hits_kind` 只用 definition/theorem/assumed_field、哈希一致 |
| M2 的 CSV | 独立解析 | **发现缺陷**：表头 11 列，27 个数据行中 **15 行**含未加引号的逗号（字段数 12–14），不能作为表格解析；已退回 M2 修复（只改引号、不改内容），修好后重核 |

一条方法记录：三个任务的 CSV 都有"字段内含逗号"的风险，而只有 M2 踩到。今后凡要求交付 CSV，主线接收时必须
独立解析一次（列数 + 空字段 + 哈希），不能只看行数自述。

## 1. H1：最小忠实类型

先定"忠实"的判据：**每个字段都必须被某个证明义务消耗；任何不被消耗的字段都应删掉**。据此，联合见证
`JointWitness D` 的最小数据是

| 槽 | 内容 | 为什么必须在类型里 | 不被消耗就删 |
|---|---|---|---|
| W1 | 来自 D 的**来源关系**：一条记录，说明该对象由 D 经原文允许的操作得到（箭头复合的具名链，而非字符串标签） | 没有它，"同一 native q"就只是巧合 | 是 |
| W2 | cQ3 侧结构：value-BPS 结构 poly-morphism 的**orbits 数据**（不是选定的一个同构）＋ Galois/单位作用 ＋ local↔global localization maps | 原文 cQ3 保留的正是这些结构；删掉就退化为裸 determinant | 是 |
| W3 | 代表选择的不定性：poly-isomorphism torsor 的**一个元素及其不变性证明**（读数沿 torsor 不变） | 形式商层面对象只到 orbit 为止；不记选择就无法比较读数 | 是 |
| W4 | cQ4 侧：同一列的 log-Kummer 路径（迭代词）＋ 归一化数据（tensor power M、twist、degree 归一化） | 原文允许任意 log-link 迭代；读数依赖这条路径 | 是 |
| W5 | 两个读数：`vQ : JointWitness → ℝ`（native 解释）与 `vOut : JointWitness → ℝ`（输出解释），**由同一对象定义** | 比较必须落在同一个对象上 | 是（但定义方式受 H3 约束） |
| W6 | 允许性：该对象的输出属于原文允许输出/hull 族 | 否则它不是"实际允许输出" | 是 |

**明确不在类型里**：q₀ ≤ B；`vQ = q₀`；`vOut ≤ B`；任何"该对象与原文对象相同"的字段。原文等价性是研究目标，
不是数据。

**最小性检验**：删掉 W1 后 W5 仍可定义（对任意对象都能算体积），但 W6 与"同一 native q"一起崩掉——这正是
source-analysis §3 指出的 `EtaAlg.realisation` 与 `ValBPS.Iso` 的缺口（前者只给输出入 hull，后者保留每个
local pilot 但没有"输出区域 degree 等于 native q-degree"的字段）。删掉 W3 后，比较只能对某个代表成立，
不能下降到形式商——`etaAnab_eq_etaQ_iff` 已经把这个量准确暴露为 `logVol(out ι S) = qPilot.lhs`。

**H1 的开放问题（交回主线，不由机械任务回答）**：W2 的"结构 poly-morphism"到底保留到哪一层才算够——
只保留 `Galois/单位` 作用加 localization，是否足以约束 pilot 读数；还是要保留到 line-bundle 范畴。M1 的箭头清单与
M3 的接口字段表是判断这两者的输入，但判断本身不能由"源码没要求"推出"原文缺"。

## 1′. M1/M2 回填后必须改设计的三处

M1（`handoffs/core-backward-2026-10-23/M1/`，已抽查原文 9237–9264、9863–9872）与 M2
（同批次 `M2/`，已抽查 8135–8144、11022）把三件事变成硬约束，不能只当补充说明：

**(a) 商类型不是"集合层 orbit"就能了事。** M1 指出："structure poly-morphism" 在原文中
是 `Aut(det^{⊗M}(φ(P_B)))` 对某个线性 morphism 的**orbit**（集合层），而 cQ3 的结论对象被明确称为
**formal / stack-theoretic / diagram-theoretic 商**，并且是**相对于** coarse/set-theoretic 商而言的。
因此 W3 不能只写"读数沿这个 orbit 不变"：必须先记录所用商是哪一层。若模型只实现集合层 orbit，则它**弱于**
cQ3 的陈述，`vQ = q₀` 的事实不能顺移。这是 H1 的首要问题，不是记号问题。

**(b) 环境范畴未声明。** M1 指出：图中的下排节点索引是 `(n,m)`，上排是 `(n,◦)`（整条纵线），
且第一条竖箭的余域"包含一个参数 `†D>`"；但 16 个节点被画成同一类，`∼→` 与 `↑` 同处一图，
而"存在一个同时容纳两排的环境范畴"原文并未声明。因此 W2 的 localization maps 在**类型上**还没有着落：
在未定环境范畴之前，K1 无法把这条 zig-zag 写成箭头链。设计上应把"环境范畴"显式列为 H1 的待定项，
而不是默认它存在。

**(c) IPL 复合是族索引，不是单个箭头。** 原文 9863–9864 说的是 `linking isomorphisms of
"intermediate" prime-strips are given by composing …`，即对每个中间 prime-strip 给一个复合，
而非给一个具名对象的自同态。所以 H2 第一步不能写"具名链"就完事：要么把它忠实写成**族索引**的复合，
要么显式携带一个中间对象的选择，并在下降时证明结果与该选择无关（与 W3 同一件事）。

**(d) 归一化方块前有三件待钉死的记账。** M2 的三条发现直接进入 H3：
i. 从 M 次 tensor power 的读数**没有"除回"映射**；(Ob4)（8135–8144）与 (Ob4-3)（8185–8189）都只是
   **断言**"不会产生实质问题/不影响 log-volume"，没有定量界、没有不变性证明。所以"读数等于 q₀"之前，
   必须先补这一条。
ii. **M 从未被赋值**；(Ob3-2) 只说它是"唯一确定的正整数"，与 R3.1.1(iv) 的 `N_E` 只是 `cf.`。需要证明
   hull determinant 的 M、q-pilot 侧被比较的 M 次 tensor power、以及 (Ob4-1) 的 degree-M Frobenius
   是同一个 M。
iii. (xi-d) 在 11022 写 `[suitably normalized, with respect to j ∈ |F_l|]` 而**无公式**，Step (x) 用的是
   `j ∈ F_l^⋆` 上的**平均**，两处未声明相同；Prop 3.9(iii) 的全局 log-volume 等同 arithmetic degree 又只
   "relative to a suitable normalization"，该归一化全文未写。故 `vQ = q₀` 只有在 j-归一化与全局归一化
   两条约定对齐后才有意义。

## 2. H2：构造与下降

构造必须**沿原文实际操作**，而不是先造一个满足条件的对象再补来源：

1. 沿 IPL 的复合（M1 给出端点清单）给出**族索引**的链：固定 q-prime-strip → 各中间 prime-strip → 输出。
   原文把它写成 `linking isomorphisms of "intermediate" prime-strips are given by composing …`（9863–9864），
   因此每一步是对每个中间对象给一个复合，而非一个具名箭头。**取逆的地方标记取逆**（IPL 只在前两条下横箭
   与复合本身用 `inverses`）；端点不匹配处记录 `UNRESOLVED`，不得用"应当相同"补全。若要把它压成单个对象，
   必须显式携带中间对象的选择，并在下降时证明与该选择无关。
2. 中间 prime-strip 同时充当算法输入与 native q 的 Kummer 输入，这是同一性的来源，不是巧合。
3. 下降：形式商/stack 层面对象定义到 orbit 为止。因此 W3 的不变性证明是**下降的前提**，不是装饰：读数必须
   因子化通过 `JointWitness / 不定性` 才谈得上比较。
4. 下降后要检查的核心问题（原文最易被忽略处）：**"同一 native q"这条关系是否还在**。若只剩相同的标量值，
   则下降掉了本应保留的关联（iQ5 的警告），此路线即失败，而不是"数值上成功"。

**禁止**：把 IP 的"任意存在同构"当成复合链；把一个 poly-isomorphism 选成一个普通同构；把 hull 扩大当成
下降的替代（扩大改变的是族，不是商）。

## 3. H3：读数交换与路线取舍

### 精确对象路径（优先）

需要两块证明，缺一不可：

- **方块交换**：`vOut` 与 `vQ` 由同一对象、同一归一化数据算出，交换图在 tensor power M / twist / degree / log-link
  迭代下成立。这是 K3 的实质内容；局部对数定理不能替代它。**前置条件**（见 §1′(d)）：先钉死 M 的唯一性与
  "除回 M 次 tensor power"这一步，再对齐 (xi-d) 的 `j ∈ |F_l|` 归一化与 Prop 3.9(iii) 的全局归一化；
  这三项未定之前，"交换图成立"没有明确含义。
- **native 读数精确**：`vQ w = q₀`。注意方向：这是**证明**，不是把 `vQ` 定义成 q₀；且它隐含上述归一化约定。

得到 `q₀ = vQ w = vOut w ≤ B`，即 G0。

### 近似输出路径（备选，量词必须写全）

```text
∀ ε > 0, ∃ w : JointWitness D,
    SameNativeQ w  ∧  q₀ − ε ≤ vOut w  ∧  vOut w ≤ B
```

- 只求数值不等式时成立即可，**不需要**先构造达到极限的同一个 J。
- 若 `vOut` 通过外逼近 inf 定义，则必须保留正确量词：对**已给定的 E**取上方 superset 的 inf，不能从这个较大
  超集反推原输出达到 q（core-order-bridge 的 `inequality_of_outer_coverage` 正是保留这一前提的那件工具）。
- 每次 ε 可以是不同 witness，但每个都必须是**固定 D 与同一 native q** 的来源关系。

### 紧致性路线（可选，K6）

只有当实际方案只给有限精度兼容数据、且确实需要一个满足无限多条件的共同 J 时才接。它的前提是实际的参数空间、
闭约束、输出 USC 与**联合**有限近可行（不是各自可满足）。`exists_joint_threshold_of_compact` 给的是
`q ≤ score x`，不是 equality；而 `V ≡ q₀ + 1` 说明 USC 本身给不出 equality。source-analysis §6 的六类风险
（正测度不自动闭、L¹ 不对称差、Hausdorff 改变类型、有限支持在极限丢失、全局 USC 需控求和、输入体积性质≠输出
体积性质）必须先逐条处理，否则这条路线只是形式上成立。

## 4. 与现有工具的接线

| 现有 | 只在何处使用 | 不承担 |
|---|---|---|
| `core-order-bridge` | 外逼近 inf 的量词与条件性数值比较 | 原始允许输出族与其 inf 实现 |
| `core-compactness` | 联合有限近可行 → 同一全局 witness；反例说明"各自可满足"不够 | IUT 的参数空间、拓扑、联合近可行性 |
| `EtaAlg.realisation` | 输出入 hull 的一个方向 | 原算法实现与 native 来源对应 |
| `SHESides` / `SHEq` | 记录两侧标签独立性 | 不能当"原文 SHE ⇒ native 比较" |

## 4′. M4 的复用边界（已抽查定位）

M4（`handoffs/core-backward-2026-10-23/M4/`，8 条命中）给出的事实要与"能拿来用"分开读：

| 需求 | 现有最接近的东西 | 到什么程度 |
|---|---|---|
| 作用 + 等变 morphism | `Iut.Frobenioid.OrbitObj` / `OrbitHom`（`Iut/Frobenioid/TemperedBase.lean:43,52`） | **已覆盖**：等变是字段，且 `surjective`(87)、`injective_of_mono`(164)、`bijective_of_isFSM`(178) 是真题 |
| 结构 poly-morphism / orbit 数据 | `OrbitObj` + `RlfMuStrip.Iso` / `ValBPS.Iso` | **部分**：没有 poly-morphism 类型；不定性被**重构**成"值部分是 subsingleton"（`ValBPS.valIso_subsingleton:296`）。这与 W3 不是同一件事——见 §1′(a) |
| local + global + localization | `Iut.ThetaLink.RlfMuStrip`（`PrimeStrip:159–163`） | **部分且被削弱**：只经 realified value groups 与 `localPilot` 保留，`ρ_v` 不是字段；**没有任何下降/粘合陈述** |
| pullback / base change 保结构 | `IsFrobenioid.pullback_surj`（`Defs.lean:251`） | **是假设字段，不是定理**；存在性只在 model Frobenioid 与退化的 angular 情形证明；沿 log-link/Θ-link/cQ3/cQ4 一条都没有，商下降更是空白 |
| determinant / tensor power 的度自然性 | `abs_det_archIndMap`（`GalKummerAll:327`）、`degree_hom`（`Global:305`）、`degree_frobenius`（`Global:328`） | **分离**：archimedean 只有 |det| = 1；`degree_frobenius` 只是把证书字段投影出来；真正可用的是 `degree_hom` 与 Iut4Sec1 的 `[L:K]` 缩放（且 IUT IV Def 1.9(ii) 的商刻意未声称） |

结论对 H2 直接成立：**`external/iut` 里没有任何东西构造联合对象或其 localization/下降**。可复用的是三块零件——
orbit 范畴、model-Frobenioid 的 pullback 构造模式、Iut4Sec1 的 base-change 度定理；拼装与下降仍是主线的事。

环境注意（M4 记录）：`external/iut` 固定的 mathlib 与本地 `85e3a25e`（v4.34.0-rc2）**不同版本**，任何移植前必须
先解决版本差，不能假定签名可直接搬用。

## 5. 本轮不做的

不构造 J；不证明原文与本模型等价；不把 `tautological` 登记为已证；不把任何 hull 子区域的数值可达性当成输出满射；
不因缺少紧致参数空间就宣称原论证失败。以上任一项要做，都需要新的 Lean 证明与编辑器零诊断准入，不在本轮静态准备
的范围内。
