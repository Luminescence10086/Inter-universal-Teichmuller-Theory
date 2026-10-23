# N11 — 工具设计卡（只选 2 条路线）

日期：2026-10-23。目录：`handoffs/non-lean-2026-10-23/N11/`。
纪律：本文件里 **数学推导一律 `UNVERIFIED_MATH`**，直接出处事实标 `SOURCE_FACT`，有限模型运行标 `EXPERIMENTAL`；
没有 `Lean`、没有 `Lake`、没有编辑器。**两条卡都不是结论，也都不是"新定理"**。

## 0. 为什么是这两条（另外两条为何不选）

- **不选路线 1（群胚、下降、Galois 型重建）**：它最自然的产出是"联合兼容选择"的存在性，而那是**比 (9-1) 更强**的族条件。
  N03 的 `O5` 与 `existence_does_not_force_invariance` 已经证过：存在一个 `S` 不蕴含全族不变。把下降障碍当成 (9-1) 的
  必要条件，正是 N03 §4 明令禁止的那种加强。其次，`Ind3` 目前只有集合结构（`Ind3.lean:213`）加上
  `ind12_acts_on_S` 给出的一个置换 `τ`（`EtaAlg.lean:112`），没有可用的群胚/叠结构——障碍类定义出来是空壳。
- **不选路线 2（逆极限、紧致性、有限可满足性）**：`Region D` 上仓库**没有引入拓扑**，`Ind3` 也不是滤过族；
  契约自己警告"不能默认紧致性成立"。要做必须先造拓扑、再证约束闭＋有限交性质，等于新建一层，超出本轮边界。
- **选路线 3 → N08**（非阿几何/格/有限模）：因为 `hull` 在仓库里**逐字就是** `scaledIntegral b`（即 `b·O`），
  而 "是不是最小 hull / 有限模拉回是不是只是容器" 逐字就是格的饱和问题——可算、可否证。
- **选路线 4 → N07**（约束求解与优化对偶）：因为 `realisation` 只给**包含**（`EtaAlg.lean:123-125`），
  目标是**等式**（`EtaAlg.lean:151`）。"上界证书 vs 达到的见证"就是这条缺口的精确形状。
- **共同底座（这是发现，不是偷懒）**：两张卡都在"指数/对数坐标 + 单调读数"这一个归约下工作，因此能放进**同一个**
  有限模型脚本 `toy_check.py`（Part A / Part B）里跑。代价是：卡 2 的 Farkas 型对偶只在归约成立后有效，
  而归约成立的判据正是卡 1 的 `A1`/`A3`。**卡 2 的有效性依赖卡 1 的审计结果**——这一依赖必须显式挂在依赖图上。

**缺项编号约定**（本文件新增的局部编号，只为指向 N08/N07 执行卡里的具体句子，不改原卡）：
`G1` = 从 `ℚ_p^n/ℤ_p^n` 模型走向真实系数环、局部域乘积、可能分歧与分式参考格；
`G2` = 原始 hull 是否恰为每坐标非零的 `λ·O`；`G3` = 何时有限模拉回只是一个容器；
`G4` = 同一 Haar 归一化到全局权重的桥梁；
`H1` = `EtaAlg.realisation` 与原文执行之间缺的对应；`H2` = 不把分别存在的选择拼成联合合法见证。

---

# 卡 1：T3-LAT「容器–最小 hull 审计器」

- 路线：**3（非阿基米德几何、格与有限模）**
- 填补：**N08-G2**（"原始 hull 是否恰为每坐标非零的 `λ·O`"）、**N08-G3**（"何时有限模拉回只是一个容器"），
  并为 **N08-G1** 的第一小步（分式参考格 `λ·O` 的类型）给出可执行入口。
- **本轮已得到的部分答案（见 §1.3 A1'）**：对 LANA §5.2(d) 的**模 hull**，答案是"是"——仓库的
  `scaledIntegral b` 忠实实现了它；真正未决的是 LANA §8.1(f) 的**环 hull**（"with respect to the ring structure at (1,1)"）。
  这不是折扣，而是把 G2 从一个含糊的问题切成"已回答的一半 + 未决的一半"。
- 不填补：**N08-G4**（同一 Haar 归一化到全局权重的桥梁）——本卡完全没碰（LANA §5.2(e) 已把归一化钉死，
  但仓库侧是否对齐属 N06-`O6`，本卡未查）。
- 状态：`UNVERIFIED_MATH`（设计）＋ `EXPERIMENTAL`（Part A 已跑，见 §1.5）。

## 1.1 精确输入（类型 + 从哪来）

| # | 输入 | 类型 | 来源 |
|---|---|---|---|
| 1 | `D : InitialThetaData.{0}` | 固定参数（域、素数集、`bpsDegrees`） | `Iut/Wall/Ind3.lean:55` |
| 2 | 容器 `VC D`，capsule `i : Fin (VC D).proc.length`，有理位 `vQ : RationalPlace`，标签元组 `c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ` | `(VC D).AdmissibleRegion i` | `Ind3.lean:58–123` |
| 3 | 逐坐标分量 `vcIComp D i vQ c : Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.placeSect vQ c))` | `Set _` | `Ind3.lean:58–62` |
| 4 | hull 系统 `LocalTheory.hull D.placeSect (nC D)`：`HullRegions`、`scaledIntegral b`、`hull_le`、`hull_mem_hullRegions` | `HullSystem` | `Ind3.lean:138–147, 180–207` |
| 5 | 测度 `LocalConstruct.haar vQ _`、`haar_proj_scaledIntegral_lt_top` | Haar | `Ind3.lean:144–147`；`Rss.lean:158` |
| 6 | **待审计对象**：每个 `(i,vQ,c)` 的指数集 `E ⊆ ℤ^J`（`J` = 该 packet 的局部坐标/tensor 因子索引），取自 `vcIComp` | `Set (ℤ^J)` | **取法本身 `PROPOSED_INTERFACE`**：须待 N04 的系数环/order 接口落定后才能定义 |
| 7 | **hull 的两个定义**：`S^hol` = 含 `S` 的**最小 `VC(O)`-子模**（§5.2(d)）；以及"**w.r.t. the ring structure at (1,1)**"的 hull（§8.1(f)） | 原文定义 | `LANA-interim-report-2026-07.txt:1338–1340`、`:1923–1927`（`SOURCE_FACT`） |
| 8 | 归一化口径：`vol(VC(O)) = 1`、`p_v` 作用为 `p_v^{-1}`、`log-vol(p_v·VC(O)) = −log(p_v)`，即 procession-normalization | 定义 | `txt:1341–1348`（`SOURCE_FACT`；仓库侧是否对齐属 N06-`O6`，**未查**） |

审计结果的类型（这就是要形式化的形状）：

```
Audit i vQ c  :  Σ (b : ∀ c', IsUnit (b c')),  -- 候选的 λ（每坐标下界）
                 Bool                          -- true = 已是 box
                 ⊕  Σ (φ : J → ℤ) (x : Total), -- 否则：整数分离泛函 + 见证点
                    (∀ y ∈ vcIComp …, φ·v(y) ≥ 0) ∧ φ·v(x) < 0
```

`⊕` 的两支互斥且穷尽（`Farkas` 型）；`φ` 就是"这条不是 box"的**可复核证书**，不是口头结论。

## 1.2 拟输出

1. 每 `(i,vQ,c)` 的**指数下界表**（即 `b_c` 的具体值；这就是"每坐标 `λ·O`"里的 `λ`）。
2. 三值判定：`BOX` / `NONBOX(φ,x)` / `UNKNOWN`（超规模上限返回 `UNKNOWN`，不许猜）。
3. 对 `NONBOX`：`μ(box) = p^{-Σm}` 与 `μ(conv E)` 的对照——即"把容器当 hull 读数"会偏多少。
4. **归约条款**：对**模 hull**，由 A1' 预言全部 capsule 均 `BOX`（若出现 `NONBOX`，则 A1' 被否证，见 §1.6 F1）；
   对**环 hull**，只要出现一个 `NONBOX`，就说明两种 hull 在该 capsule 上不等，G2 的未决一半得到否定答案，
   且 G3 的答案是"有限模拉回只是容器"。

## 1.3 关键假设（逐条编号）

- **A1（定义性，`SOURCE_FACT`）** `hullOf D U ∈ HullRegions`，且 `HullRegions ⊆ {scaledIntegral b : b 为逐 label 的单位}`
  （`isHullRegion_of_mem_hullRegions`，`Ind3.lean:142`；`H.isHullRegion_of_mem`，`:190`）。
  故仓库的 hull 是**按 packet 索引 `c` 的 box**：每个 `c` 只取一个 `b c·O_c`。
- **A1'（本轮已核的对照，`SOURCE_FACT`）** LANA §5.2(d) 把 `S^hol` 定义为"含 `S` 的**最小 `VC(O)`-子模**"
  （`txt:1338–1340`）。`VC(K)` 是 `VC(O)`-模且 `VC(O) = ∏_v LocVC(O)_v`（`txt:1333–1337`），
  于是 `VC(O)`-子模**逐坐标**就是 `b_v·O_v` 形状的乘积。**所以 A1 里的 `scaledIntegral b` 不是仓库的权宜之计，
  而是 §5.2(d) 模 hull 的忠实实现：对模 hull，N08-G2 的答案是"是"。**
- **A2（真正未决的一半，`SOURCE_FACT` 有出处 / 内容 `PROPOSED`）** §8.1(f) 取的 hull 是
  "**w.r.t. the ring structure at (1,1)**"（`txt:1923–1927`），不是 `VC(O)`-**模**结构。环乘法把 tensor 因子耦合起来，
  所以环 hull ⊆ 模 hull，一般**严格**更小。于是卡 1 的实质是**比较两个 hull**（`hull_module` vs `hull_ring`），
  而不是"仓库的 box 对不对"。
- **A3（`PROPOSED_INTERFACE`）** 指数集 `E` 可从 `vcIComp`（tensor 张成）无歧义读出：`J` 的选取与 `tensorLogShell`
  的初等张量呈现相容。
- **A4（待判，不是假设成立）** `hull_ring`（环结构在 `(1,1)` 处）的读数是否等于 `hull_module` 的读数。
  仓库自陈取了 deviation（`Ind3.lean:32–38`，引 IUT IV Thm 1.10 与 `WallEquiv/VcI.md`），但它**只**对准了
  §5.2(d) 的模 hull；§8.1(f) 的环 hull 不在它的读法里。**本卡的输出就是判这一条。**
- **A5（`PROPOSED`）** 环 hull 的指数集是**耦合**闭包（不是逐坐标下界）；实/复情形有完备 Reinhardt 域
  包络 = 对数凸包的定理论可作模型，但**非阿、且是环而非模**的类比没有在本轮引证到来源，用则须补引。
- **A6（`PROPOSED`）** 有限模拉回（`tensorLogShell` 的 `ℤ_p`-张成 → 有限商）只有在格**饱和**时才等于最小 hull；
  饱和取 `L^sat = (L ⊗ ℤ_p ℚ_p) ∩ V`。不饱和 ⇒ 拉回只是容器。`txt:1330–1332` 说 `LocVC(O)_v` 是把
  `⊗_{ℚ_v} ℚ` 换成 `⊗_{ℤ_v} ℤ` 后"**再取整闭包**"——整闭包 ≠ 饱和，这一句是本条的唯一来源线索，`UNRESOLVED`。

## 1.4 迁移来源（数学分支 + 为什么类比不是换词）

- **复/实多复变：完备 Reinhardt 域与对数凸包。** 迁移的落点是 §8.1(f) 的**环** hull。不是换词的理由：
  hull 在仓库里的定义**就是** `scaledIntegral b`，即 `b·O`，一个**分式格**；`v(x)` 把"`x ∈ b·O`"逐字翻成
  "`v_j(x) ≥ b_j`"，于是"取环 hull"变成一个**整数指数集上的闭包计算**——闭包是逐坐标的（模 hull）还是耦合的
  （环 hull）**是个数学问题，不是一个词**：耦合时能写出分离证书 `φ`，能被有限例打脸（§1.5 的两条 `φ` 就是
  打脸的证书）。若只是术语替换，就写不出 `φ`，也写不出"环 hull ⊆ 模 hull 且一般严格"。
- **非阿几何/格论：`ℤ_p`-格的饱和、Smith 标准形、index。** 不是换词的理由：`tensorLogShell` 被定义为初等张量的
  `ℤ_p`-张成（`Ind3.lean:40–43`），所以"这个容器是不是最小 hull"**逐字**是"这个 `ℤ_p`-张成在其 `ℚ_p`-张成里是否饱和"
  ——一个整数不变量（index / `p`-挠），算得出来、可复核。
- **热带几何 / Newton 多面体**：区域由单项式不等式给出时，指数集凸包就是其 Newton 多面体；对数凸 = 通常凸。

## 1.5 最小可检验例（已实跑，`EXPERIMENTAL`）

`toy_check.py` **Part A**，`p = 2`，`n = 2`，坐标 `v_j = val_2(x_j)`；`B(E) = ∏_j {v_j ≥ min_j E}`，
`μ` = `ℚ_2^2` 上 Haar：

| 例 | `E` | `B(E)` | 判定 | `μ(B)` vs `μ(conv E)` |
|---|---|---|---|---|
| A1 | `{(0,0),(0,1),(1,0),(1,1)}` | `=E` | `BOX` | 1 vs 1（无差） |
| A2 | `{(0,0),(1,1)}` 对角 | `{v_1,v_2 ≥ 0}` | `NONBOX`：`x=(0,1)`，`φ=(1,−1), c=0`（`φ|_E = 0 ≥ 0`，`φ(x) = −1 < 0`） | 1 vs **0** |
| A3 | `{(0,1),(1,0)}` 反对角 | `{v_1,v_2 ≥ 0}` | `NONBOX`：`x=(0,0)`，`φ=(1,1), c=1` | 1 vs **0** |

命令与结果：`py -3 toy_check.py` → exit 0，`RESULT: ALL PASS`，日志 `N11/toy_check.log`。
**读法（`EXPERIMENTAL`，只在这个有限模型里）**：一旦指数集不是 box，逐坐标 box 严格大于"耦合闭包"；
两个 `NONBOX` 例里后者测度为 0、**甚至不是 admissible 区**（`hpos` 失效），两种 hull 约定在这里不可比。
**故"hull = 逐坐标 `λ·O`"只在模 hull（§5.2(d)）下无条件成立；换成环 hull（§8.1(f)）它就有内容了**——这正是
N08-G2 的可判定形式。
**局限（必须写明）**：
1. 例里的"耦合闭包"用的是 `conv E`（对数凸包，Reinhardt 传统的模型），**不是** `O_{(1,1)}`-乘法下的半群闭包；
   真正的环-hull 模型本轮**没有**建（见 §1.6 F5）。
2. toy 在局部 `v` 坐标上跑，不等于已算出仓库 `c`-索引的 box（`A3` 仍是 `PROPOSED`）。

## 1.6 失败条件（什么观察会否证这条路线）

- **F1（对"模 hull"这一半，这是**预言**不是失败）** 由 A1'，模 hull 下审计**应当全 `BOX`**。
  若真跑出 `NONBOX`，说明"`VC(O)`-子模 = 逐坐标 `b·O` 之积"这一步不成立（例如 `LocVC(O)_v` 的"整闭包"
  `txt:1330–1332` 引入了耦合），则 A1' 被否证，卡 1 必须退回"取法未定"。
- **F2** 若 `vcIComp` 的 tensor 呈现使 `E` 不可逐坐标读出（`φ` 无法写成坐标线性型），则 A3 失效，
  审计必须整体重建在张量格上（多半无法逐坐标化）。
- **F3** 若某个 `NONBOX` 例的耦合闭包是**满维**的，则"不可比"降级为"有限对数体积差"，卡的强形式被削。
- **F4** 若 §8.1(f) 的环 hull 经核实就是模 hull（例如 `(1,1)` 处环结构在 `VC(O)` 上的作用已经因子化），
  则 A2 的两半重合，环 hull 这一半**整块落空**，卡 1 只剩 A1' 的确认。
- **F5（本轮已承认的缺）** 若不允许引入环-hull 的半群闭包模型，则 §1.5 的 `conv E` 只是**现象展示**，
  不能当作环 hull 的证据；此时卡 1 的可检验内容缩为 A1'（模 hull 的忠实性）＋ A6（饱和 vs 整闭包）。

## 1.7 需要 Lean 的后续命题（一句）

`hullIdem_iff_mem : ∀ (i) (vQ) (U : Region D), hullOf D U = U ↔ U ∈ ((LocalTheory.hull D.placeSect (nC D)).system i vQ).HullRegions`
—— hull 幂等当且仅当 `U` 本身已是一个逐坐标 `b·O`。它把"容器是不是最小 hull"变成一个可判定的成员判定。

---

# 卡 2：T4-ATT「达到–证书二分器」

- 路线：**4（约束求解与优化对偶）**
- 填补：**N07-H1**（`EtaAlg.realisation` 与原文执行之间缺的对应：**包含 ≠ 等式**），亦即 **N03 的 `O1`**
  （"存在 `S` 使 `logVol(out ι S) = qPilot.lhs`"）；并对 **N07-H2** 提供**否定性服务**：
  一旦给出严格证书，任何"联合见证"都不存在，不必再拼。
- 不填补：`O6`（归一化台账）、`O7`（`qPilot.lhs` 是否就是原文的 `q`）。
- 状态：`UNVERIFIED_MATH`（设计）＋ `EXPERIMENTAL`（Part B 已跑）。

## 2.1 精确输入（类型 + 从哪来）

| # | 输入 | 类型 | 来源 |
|---|---|---|---|
| 1 | `A : EtaAlg D`：裸字段 `out`、`ind12_acts_on_S`、`etUnitOnly`、`realisation` | `struct` | `EtaAlg.lean:96–125` |
| 2 | `ι : A.Choice (A.qBPS h₂) h₁`、`S : Ind3 D` | 选择 | `EtaAlg.lean:141`；`Ind3.lean:213` |
| 3 | 目标值 `t := (concreteVariantData D).qPilot.lhs`；归约 `η` 相等 ⟺ 该标量等式 | `ℝ` | `EtaAlg.lean:151` |
| 4 | **上界证书的现成零件**：`logVol_le_logVol_hullOf`、`logVol_le_vcI`、`logVol_le_rhs` | lemma | `Ind3.lean:138, 244`；`EtaAlg.lean:204` |
| 5 | `Ind3` 的读数像恰为 `(−∞, logVol(hull(VC(I)))]` | theorem | `Ind3.lean:253` |
| 6 | 已证的"塌缩"定理：任何 `logVol(out) = −s|log q| + logVol(S)` 的 `EtaAlg`，其 wall ⟺ Scholze–Stix 不等式 | theorem | `Constraints.lean:201` |

## 2.2 拟输出

对每个 `(A, ι, t)` 输出**三值分类**（不是二值！）：

- `WITNESS (S)`：`S : Ind3 D` 且 `logVol D (A.out ι S) = t`——可交给 Lean 复核的等式；
- `CERTIFICATE (c)`：`c < t  ∧  ∀ S : Ind3 D, logVol D (A.out ι S) ≤ c`——**统一否证一切见证**；
- `UNDETERMINED`：两者都不能从已声明字段推出（**今天真实的 `A` 的正确答案就是这个**）。

附属输出：分离对象 `M(A,ι) := sup_S logVol (A.out ι S)`；若无法计算，必须写明 `UNDETERMINED` 的**原因**
（缺哪一个声明项），不得默认 `M` 不存在。

## 2.3 关键假设（逐条编号）

- **B1（`SOURCE_FACT`）** `logVol` 对区域包含单调。`logVol_le_logVol_hullOf`（`Ind3.lean:138`）＋
  `processionVol_le_of_packetVol` / `packetVol_le_of_subset`。
- **B2（`SOURCE_FACT`）** `Ind3` 的读数像恰为 `(−∞, logVol(hull(VC(I)))]`（`Ind3.lean:253`）。
  正是这一条把"达到 `t`"变成**阈值问题**，而不是无界搜索。
- **B3（`SOURCE_FACT`）** `(T3)` 只给**包含**：`IsAdelic ∧ InHullOfImage`（`EtaAlg.lean:123–125`），
  文件头亦自陈 "asking only for the hull is weaker"（`:46–54`）。它**不给** `S ↦ out ι S` 的满射性。
- **B4（`SOURCE_FACT`）** 分类在 `ι` 的 `(Ind1)/(Ind2)`-轨道上良定义：`out((BPS.Iso.mk α _).trans ι) S = out ι (τ S)`
  （`EtaAlg.lean:112`），故 `S` 上的像集不变。
- **B5（纪律）** 分类为 `UNDETERMINED` 时就输出 `UNDETERMINED`；**不得**用"各自存在的选择"拼成联合见证
  （N03-`O5`；`existence_does_not_force_invariance`）。

## 2.4 迁移来源（数学分支 + 为什么类比不是换词）

- **线性/凸对偶、Farkas 引理。** 上界证书 = 对偶可行解；达到 = 原问题有最优解 + 互补松弛；
  一般的 sup 不必然达到（实分析）。
- **不是换词的理由**：在对数/指数坐标下，`logVol` 是**线性**泛函、包含是**锥序**，于是"对偶"是一个**真正的线性泛函**，
  证书是一条**真正的 Farkas 型不等式**；仓库里的证书（`logVol_le_logVol_hullOf` 加 S–S 不等式，
  `Constraints.lean:201`）**逐字**是这种形式。若不是对偶而是换词，就写不出"`c < t` 且对**所有** `S` 成立"这条
  与见证**互斥**的陈述。
- **弱化处（必须写清）**：`Ind3` 在对象空间**不是**多面体，Farkas 只在指数坐标归约之后可用；那个归约正是卡 1 的
  `A3`。**所以卡 2 的有效性以卡 1 为条件**（§0 已挂）。
- **约束求解一侧**：SAT/CSP 里"存在见证"是可行性、"上界证书"是不可行性的对偶证明；N10 的有限约束表正是这一支的输入形态。

## 2.5 最小可检验例（已实跑，`EXPERIMENTAL`）

`toy_check.py` **Part B**，区间模型（`Ind3` 读数像的模型）：`M = logVol(hull) = 1`，目标 `t = 3/4`。

| 模型 | `μ(out S)` | 像 | `(T1)/(T2)/(T3)` | 判定 |
|---|---|---|---|---|
| M1（identified-copies 形状） | `μ(S)` | `[0,1]` | 全满足（`μ ≤ M`） | `WITNESS`：`S = [0, 3/4]`，且 `⊆ hull` |
| M2（同样字段、另一个 `out`） | `min(μ(S), 1/2)` | `[0, 1/2]` | 全满足（`μ ≤ M`） | `CERTIFICATE`：`c = 1/2 < 3/4` |

命令与结果：`py -3 toy_check.py` → exit 0，Part B 六项 `PASS`（含 "fields do not decide"）。
**读法（`EXPERIMENTAL`）**：两个对象在 Part B 能看见的**每一个已声明字段**上一致，却一个达到、一个不达到。
故"已声明字段"给出的答案是 `UNDETERMINED`，要判定必须**多声明一项** `M(A,ι) = sup`。
这就是 N07-H1 的精确形状：`out` 是裸字段，`realisation` 只给包含。
与仓库一致：`Constraints.lean:201` 已证"log-vol 形状相同 ⇒ wall 就是 S–S 不等式"，
即**真正的判别式在 log-vol 上，不在 `out` 的结构上**。

## 2.6 失败条件（什么观察会否证这条路线）

- **F1** 若对所有满足 `(T1)–(T3)` 的 `A`，分类**恒为同一类**（例如恒 `CERTIFICATE`，经 S–S 不等式），
  则三值退化为单值，卡 2 与 `Constraints.lean:201` 重复，**必须撤回**。
- **F2** 若有人要求"仅凭 `(T1)–(T3)` 给出判定"，则工具**不可能**成立——Part B 就是反证。
  这只否证卡的**强形式**；弱形式（要求多声明 `sup` 一项）仍成立。
- **F3** 若产出的 `WITNESS` 元素不在 `Ind3 D` 内（例如落在 hull 之外），是**假阳性**，必须拒绝。
  Part B 里对 `S = [0,3/4] ⊆ [0,1]` 的检查就是这一条的最小版。
- **F4** 若 B1 的单调性对真实 `logVol` 不成立（如 procession 归一化与 packet 归一化不一致，N06 的 `O6` 未定），
  证书的符号与尺度都会变，分类不可靠。

## 2.7 需要 Lean 的后续命题（一句）

`attain_iff_le_sSup_of_downwardClosed`：若 `S ↦ logVol D (A.out ι S)` 的像在 `ℝ` 中**向下闭**
（`u ∈ 像 ∧ v ≤ u → v ∈ 像`），则 `(∃ S : Ind3 D, logVol D (A.out ι S) = t) ↔ t ≤ sSup (Set.range (fun S => logVol D (A.out ι S)))`。
—— 它把"缺的是构造，还是缺的是界"变成可判定的一句话；其假设正是 `Ind3` 已有（`Ind3.lean:253`）、而 `out ι _` **尚未**有的那一条。

---

## 3. 两张卡对 N07/N08 的映射（验收用）

| 卡 | 路线 | 填补的具体缺项 | 依赖 | 本轮**没**做 |
|---|---|---|---|---|
| T3-LAT | 3 | N08-G2：**已答一半**——对 §5.2(d) 模 hull，仓库 `scaledIntegral b` 忠实（A1'）；**未决一半**——§8.1(f) 环 hull。N08-G3：饱和 vs "整闭包"（A6，`UNRESOLVED`） | N04 的系数环/order 接口（未落定 ⇒ A3 停在 `PROPOSED`） | 环 hull 的半群闭包模型；N08-G4；N08 的 5 条待证引理 |
| T4-ATT | 4 | N07-H1（`realisation` 与执行的对应缺口：包含 ≠ 等式）、N03-`O1`；对 N07-H2 给否定性服务 | 卡 1 的归约（A2/A3） | `O6`、`O7`、N10 的联合约束实验 |

**两卡都不构成"新数学定理"**，也不把 (9-1) 推进一格；它们只把"缺口在哪、怎么否证"写成可执行的形态。
**本轮唯一的实质进展**是 A1'：把 N08-G2 拆成"模 hull 已由 LANA §5.2(d) 定死（`SOURCE_FACT`）"与
"环 hull（§8.1(f)）未决"两半——前者可以立即从 N08 的缺项清单里划掉。
