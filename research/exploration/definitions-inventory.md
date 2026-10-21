# 定义清点：IUT 对象的来源语义 ↔ 仓库最近形式化对象

状态：**候选研究笔记（correspondence ledger）**。不是新定理，不含 Lean 声明，不修改 Lean/验证器/`audit/`/`handoffs/`。本文件里每一条“原文说”都必须挂在一条笔记行号上；笔记没有记录的，写 **definition not in local evidence**，不凭记忆补写。

TL;DR (EN). Ten target objects, one row each. Recorded well enough to state: `Ism`, Kummer orbit, `log_p(O^×)`/log-shell, tensor/packet shape, Ind1–Ind3 shape, θ-as-splitting-generator. **Not in local evidence as a definition:** the Θ-link (absent), mono-analytic vs holomorphic structure (role only), holomorphic hull's minimality class (characterisation only), the possible-images admissible family (the note itself records that it was not extracted), and the Θ-pilot's data (construction locators only). No existing Lean object is an instance of any of the ten; every mapping below is a *shape* match with a stated gap. Most dangerous false bridge: reading our `ℚ_p ≃ₗ ℚ_p` / `A(k)` automorphisms as `Ism` elements.

---

## 0. 证据约定

引用形式两种，判别式很清楚：

- `笔记路径:行` —— 我们的研究笔记；其后“→”给该行**记录的**原文出处（页码/定理号是笔记记下的，不是本轮重新读取的）。
- `round2-source-cache/urahigashi-v0.8.0.tex:行` —— 本地缓存的**批评短文**（v0.8.0），它是二次文献：它能证明“该短文如此陈述”，不能证明“望月原文如此定义”。凡用它支撑对象内容，都在文中标明“短文陈述”。

证据等级（本文件自定，用于防止散文跑在证据前面）：

| 等级 | 含义 |
|---|---|
| **E1** | 定义/构造在笔记中被明确记录，且指出原文位置 |
| **E2** | 只有构造路标（“由 X 构造”），数据清单未抽出 |
| **E3** | 只记录了它的**角色/要求**（必须区分、必须实现），定义本身没有 |
| **E4** | **definition not in local evidence**（笔记明说未定义，或只有负向刻画） |

三条纪律，本文件自我约束：

1. 不使用官方 IUT PDF/缓存的页码作引用。笔记所记页码是笔记的记录；本轮不新增望月原文页码引用。第 7 节说明我做的一次**抽查**及其性质。
2. 所有 Lean 对象名与定理 id 均已 grep 验证存在（共 70 个 id，0 缺失；验证方法见第 7 节）。
3. “最近的 Lean 对象”一律按**形状**判定，不按名字判定；名字里有 `pilot` 的对象并不因此更接近 Θ-pilot。

---

## 1. 总表（10 行，一行一对象）

| # | 对象 | 证据等级 | 我们记录到的 locator（原文出处） | 最近的现有形式化对象（id 已验） | 缺口类别 |
|---|---|---|---|---|---|
| D01 | `Ism` 与 open-`H` lattice 条件 | **E1** | IUT II Example 1.8(iv) p.39（`round3-semantic-audit.md:9`）；II Def.4.9(i) p.154（同文件 `:10`） | `ContinuousLinearity.toPadicLinearEquiv`；`Shell.image_scalar_layer`；`Admissibility.LatticeAdmissible` | [definition-only] + [needs-real-arithmetic-data] + [blocked-by-missing-library: p-adic log]（仅 `L_G` 身份一项） |
| D02 | Kummer orbit / possible images family / `κ_c` | **E1**（orbit）/ **E3**（family） | II Def.4.9(i) p.154；III Cor.3.12 pp.173–174；`round3-semantic-audit.md:128–138` 明言未抽出 | `Orbit.orbitEnvelope`；`Transport.SeededFamily` / `familyImage` | [definition-only] + [needs-real-arithmetic-data] |
| D03 | Θ-pilot 及其 image region | **E2** | III Prop.3.7(v)、Def.3.8(i) p.112（`round3-realization-obligations.md:53`） | `WeightedLedger.pilotWeights`；`Transport.SeededFamily`；`LocalNumerics.Place`/`rhoNumerator` | [needs-real-arithmetic-data] + [definition-only] |
| D04 | log-shell / `log_p(O^×)` | **E1** | IUT IV Prop.1.2(i) p.10、III Rem.1.2.2(i) p.36（短文 `tex:84–89`）；`round2-realization-obligations.md:97–107` | `Filtration.integerIdealImage` + `mem_zpow_maximalIdealImage_iff_lt_valuation`；`Shell.padic_threshold_iff` | [blocked-by-missing-library: p-adic log] + [needs-real-arithmetic-data]（分歧情形） |
| D05 | Θ-link | **E4** | `GAP.md:9`（明说未定义）；`core-and-bridges.md:9,21`（仅负向刻画） | 无同构物；形态最近的是 `Transport.Reindexing`（且它是**反面**形状） | [definition-only]，且 gap 本身无法精确陈述 |
| D06 | holomorphic hull | **E2** | III Rem.3.9.5(i) p.127（`round2-source-audit.md:165`）；短文 `tex:386–389` | `Orbit.orbitEnvelope` + `envelope_minimal`/`envelope_minimal_closed` | [definition-only]（定义层）+ [blocked-by-missing-library: `R̃` 归一化] + [needs-real-arithmetic-data] |
| D07 | mono-analytic vs holomorphic structure | **E3** | `round3-realization-obligations.md:41`（列为缺失对象）；`round3-semantic-audit.md:90–100`（只给形状）；III Prop.3.1(ii) p.93 / Prop.3.2(ii) p.98 | 无。最近的是同一类型上两个作用：`Slots.relabel` 与 `Slots.slotwise` | [definition-only] |
| D08 | tensor / packet construction | **E1**（结构）/ **E2**（归一化） | 短文 `tex:71–78, 99–105`；`round2-source-audit.md:43–51` | `Slots.Tuple`（`Fin n → ℚ_p`）；`WeightedLedger.weightedLedger` | [blocked-by-missing-library: `⊗O_{k_i}` 的归一化] + [needs-real-arithmetic-data] |
| D09 | Ind1–Ind3 允许操作 | **E1** | III Thm.3.11(i) p.154、(ii) p.156（`round3-semantic-audit.md:11,114–121`）；IUT I Def.4.10 p.120（短文 `tex:328–336`） | `Slots.relabel` + `relabel_slotwise`；`Orbit.IsClosed`/`CompositionClosed`/`envelope_closed`；`Transport.Reindexing` | [definition-only] |
| D10 | splitting monoid generator θ | **E1**（关系）/ **E2**（元素缺） | III p.11（短文 `tex:283–285`）；`round2-source-audit.md:88`；`round3-realization-obligations.md:55` | `LocalNumerics.rhoNumerator`、`swap23_rho_positions`；`WeightedLedger.norm_prod_eq_zpow_totalLedger` | [needs-real-arithmetic-data] |

缺口类别汇总见第 3 节。**没有任何一行可以写成“就是”**：10 行全部是形状匹配 + 缺口。

---

## 2. 逐对象

### D01 `Ism` 与 open-`H` lattice 条件

**1) 来源记录（E1）。** `round3-semantic-audit.md:9`：

> **Ism 有强定义。** IUT II Example 1.8(iv), p.39：它是 G-equivariant ind-topological module automorphisms；对每一个 open subgroup H≤G，保持由 O×(G)^H 的像给出的 lattice。

同笔记 `:10` 记 II Def.4.9(i) p.154：×μ-Kummer structure 是 **Ism-orbit**，而且“也用所有 H 对应 lattices 的数据刻画该 orbit”；`:118` 的表把这一层单列为 “Kummer unit data”。两条都必须保留全称 `H` 量词——这是本轮最容易被压平的地方。笔记还专门禁止一个等式（`:55`）：

> 这里必须区分“单位先取 H-invariants 再映到 quotient”和“quotient 的全部 H-invariants”。原定义指定的是前者的像，不能把二者不经证明地相等化。

量词方向也记下来了（`:71–83`）：可以期待的是 `actual finite restriction of Ism(G) ⊆ A(k)`；反向扩张定理 `every T ∈ A(k) extends to an element of Ism(G)` **没有**找到或证明。

**2) 最小形式化内容（纯数学）。** 需要的数据：一个紧群 `G`（同构于某个有限扩张 `k/Q_p` 的绝对 Galois 群）；一个 ind-topological `G`-模 `U`（“`O^×μ(G)`”），即对 open `H` 的一族相容有限层 `U^H`；在每个层上一个 `Z_p`-格 `L_H ⊆ V_H`，且 `L_H` 定义为“先取 `O^×(G)^H` 的像再送到无扭商”的那个像；`Ism(G) ⊆ Aut_G^top(U)` 定义为满足 `s(L_H) = L_H`（对所有 open `H`）的自同构全体。假设：`H` 遍历全部 open 子群；层间有相容映射（`H' ⊆ H` 时的过渡）。`Ism(G)` 的群结构本身不是定义的一部分（迹、`Z_p`-格保持都不是）。

**3) 最近的形式化对象。** 三个，各只覆盖一段：
`LocalFieldAudit.ContinuousLinearity.toPadicLinearEquiv`（连续加法等价 → `ℚ_p`-线性等价；配套 `map_padic_smul`）——覆盖“从连续到线性”这一步，正是 `round3-semantic-audit.md:65` 要求不能省略的引理；
`LocalFieldAudit.Shell.image_scalar_layer`（`e '' L = L ⇒ e '' (a • L) = a • L`）——覆盖 LP0（`round3-semantic-audit.md:204–216`）“保一个格 ⇒ 保全部整数幂层”；
`IUTBridge.Admissibility.LatticeAdmissible` 与 `latticeAdmissible_unique`、`ScaleLedger.existsUnique_layer_of_auto`——把“自同构 + 它把单位球送到哪一层”写成一个联合关系。

**4) 精确 gap。** 现有对象都是**单个 `ℚ_p`-向量空间**（基域，一维）上的**单个**格上的自同构；`Ism` 是一个**带 `G` 作用的 ind-模**上、对**一族 `H` 索引的格**保持的自同构。缺的四件：(a) ind-topological 模与 `G` 作用 —— [definition-only]；(b) `H` 索引族及其相容性 —— [definition-only]；(c) `L_G = log_p(O_k^×)` 在**分歧** `k_v` 上的身份 —— [blocked-by-missing-library: p-adic logarithm]（见 D04）＋[needs-real-arithmetic-data: `e_v`、`k_v`]；(d) “实际有限限制落入 `A(k)`”就是 RI-01 本身，未证 —— [needs-real-arithmetic-data]。**不是** library 缺口的部分必须记住：把 (a)(b) 写成结构字段只是记账，不构成 RI-01（`round3-realization-obligations.md:45` 对同类偷懒有明文禁止）。

**5) 假装会怎样。** 若把 `ℚ_p ≃ₗ ℚ_p`（或 `A(k)`）读成 `Ism`，就把“单域、无 `G` 作用、单格”的自同构说成 `Ism` 元素——这会让本仓库已经证明的数十条基域定理**一次性**变成关于 IUT 的 `Ism` 群的断言，同时抹掉 `:55` 那个“像”与“全部不变量”的区别。

### D02 Kummer orbit / possible images family / `κ_c`

**1) 来源记录。** **E1** 只有 orbit 那一层：`round3-semantic-audit.md:10`（II Def.4.9(i) p.154，Ism-orbit，由全部 `H`-lattices 的像刻画）。**E3** 用于 family：`round3-realization-obligations.md:83` 记 III Cor.3.12 pp.173–174 “定义 relevant Kummer isomorphisms 与 Ind1/2/3 下的 possible images 之并”、Rem.3.9.5(Ob5) p.134 以一族 possible regions 及其 hull 表达选择独立性；但 `round3-semantic-audit.md:128–138` 明确记下**没有**抽出可调用的具体族：

> 但本次尚未抽取出一个完全具体的 dependent index type，**同时**列明：admissible c = (m, field/log coordinates, Kummer representatives, seed region, Ind1 representatives, Ind2 representatives, allowed Ind3 inclusions, synchronization data, …) / out(c) ⊆ fixed P_j / U_j = ⋃_{c : admissible} out(c)。

并给出正确诊断（`:138`）：障碍不是“原文没有 orbit 观念”，而是“尚未把所有兼容性放进一个可调用的具体 family，并证明作者使用的那条路径是这个 family 的成员”。`κ_c` 的坐标形状记在 `:96–100`（`κ_c : W_hol ≃_Qp W_an`，`χ_c := ι_an⁻¹ ∘ κ_c ∘ ι_hol`，只对 **actual admissible** `c`）；三条必须证明的相容性在 `:102–108`。短文侧（二次文献）把它写成逐 place 由 log-shell 同构搭起来、且“identifications form an `Ism`-orbit compatible with the log-shells”（`tex:304–313`，引 III Prop.1.2(vi) p.32）。

**2) 最小形式化内容。** 一个索引类型 `C`（admissible Kummer choice），每个 `c : C` 携带：`m`、域/log 坐标、Kummer 代表、seed region、Ind1 代表、Ind2 代表、允许的 Ind3 内含、同步数据；一个谓词 `Adm c`；一个输出区域 `out c ⊆ P_j`（packet 上的谓词）；`U_j := ⋃_{c, Adm c} out c`；以及每个 `c` 的 `κ_c`（保格的 `ℚ_p`-线性等价）与坐标 `ι_hol, ι_an`。orbit 那一层的索引至少是 `Ism × (选定的基准同构)`，不是一个裸 `I`。

**3) 最近的形式化对象。** `IUTAudit.Orbit.unionOfImages` / `orbitEnvelope` / `image_mem_envelope` / `envelope_covers` / `envelope_closed` / `envelope_minimal_closed`；`IUTAudit.Transport.SeededFamily` / `familyImage` / `familyImage_bound_iff`（这就是为这件事造的容器：`admissible` 是**联合**关系，`familyImage_bound_iff` 明确禁止把联合选择换成边缘选择）；`Transport.LeftAllowed` / `RightAllowed` / `coupled_choice_counterexample`；具体算例 `IUTBridge.Admissibility.marginals_do_not_force_joint`。

**4) 精确 gap。** `orbitEnvelope` 的索引类型 `I` 是**自由参数**：没有 `Adm`、没有 `κ`、没有保格、没有 `Ism`。`SeededFamily` 形状完全对，但**没有实例**——`Kappa`、`Sigma`、`State`、`admissible`、`realize` 五个字段全空。因此缺口是 [definition-only]（family 与 `Adm`）＋[needs-real-arithmetic-data]（`κ_c` 与 `out(c)` 的实际数据）。诚实的状态句：**`round3-realization-obligations.md:93` 把 RI-05 标为“当前优先审计的语义桥梁”**，而它缺的是数据，不是逻辑。

**5) 假装会怎样。** 若取 `orbitEnvelope` 且让 `I` = 全部 `ℚ_p`-线性自同构（或全部矩阵）作为 `U_j`，得到的是**过度近似族**，不是 `U_j`；于是“某个像不在容器里”变成构造性真命题（容器是我挑的），对整个 IUT 什么都没说——这正是 `round3-semantic-audit.md:319` 与 `round3-realization-obligations.md:91` 两处明文禁止的那一步。

### D03 Θ-pilot 及其 image region

**1) 来源记录（E2）。** 只有构造路标：`round3-realization-obligations.md:53` 记 III Prop.3.7(v) 与 Def.3.8(i) p.112 的 pilot 构造；`round2-source-audit.md:90`（M3 行）记“通过局部分式理想及 splitting generators 构造 Θ-pilot”。短文侧（二次文献）给得稍具体（`tex:291–304`）：Θ-pilot 由 `V_bad` 处 `Def.3.8(i)` 的 monoid 的生成元决定，由这些 monoid 元素生成的局部分式理想构造；“A fractional ideal generated by an element contains that element”。补记：`round5-joint-realization.md:136`（补充笔记）记 Def.3.8(i) 的 Θ-pilot 由 generators **up to torsion** 决定，Prop.3.7(ii),(v) pp.110–112 把 local fractional ideals 作为 subsets/submodules。但数据清单没有：`round3-realization-obligations.md:55` 把“真实 Θ-pilot 的 image-region、其积分结构、splitting generator θ 的域定义与 root-of-unity 选择，以及从抽象 pilot object 到具体 subset 的实现”整体列为**缺失对象**。

**2) 最小形式化内容。** 对每个 `v ∈ V_bad` 与 stage label `j`：一个局部 monoid（LGP-monoid）及其元素；由某元素生成的分式理想 `J(c) ⊆ k_v`；通过“其它 label 张量 `1`”的嵌入（III Prop.3.1(ii) p.93）进入 packet；生成元的 root-of-unity orbit；image region 定义为 packet 上“第 `j` 个分量落在 `J(c)` 里”的谓词。前置：实际局部域 `k_v`、`ord`、splitting monoid 的实际数据。

**3) 最近的形式化对象。** `IUTBridge.WeightedLedger.pilotWeights`（4 槽权重 `(1,1,2,1)`）＋ `pilotWeights_not_invariant` ＋ `pilotLedger_not_invariant`；`IUTAudit.LocalNumerics.Place`、`rhoNumerator`、`sourceTuple`/`targetTuple`；容器候选 `IUTAudit.Transport.SeededFamily`。必须点明：**`pilotWeights` 不是 Θ-pilot**，它只是一个权重向量；模块自己的 docstring 也只说 “the pilot-style weight vector”（`bridge/IUTBridge/WeightedLedger.lean:177–179`）。

**4) 精确 gap。** 没有域、没有 monoid、没有理想、没有元素。region 的对象是“由分式理想生成的 packet 元素集合”，我们只有“槽位上乘几”的整数。分类：[needs-real-arithmetic-data]（`k_v`：对 `Q_p` 次数 105／35 的完成域，及其 monoid 元素）＋[definition-only]（region 作为 packet 上的谓词）。**不是** library 缺口：一旦有域和理想，谓词本身是初等的。

**5) 假装会怎样。** 若把 seed region 定义成 `{g}` 或“包含所需 `g` 的某个集合”，`g ∈ SeedRegion` 立刻是同义反复，`U_j` 也变成事后挑出来的超集；这正是 `round3-realization-obligations.md:59` 明文禁止的“不能反向定义 SeedRegion”。

### D04 log-shell / `log_p(O^×)`

**1) 来源记录（E1，本清单记录最完整的一项）。** 短文（二次文献）转述 IUT IV Prop.1.2(i) p.10（`tex:84–86`）：

> If `p` is odd and `e_k ≤ p−2`, then `log_p(O_k^×) = {z ∈ k : ord(z) ≥ 1/e_k}`; so for `z ∈ k^×` and `n ∈ Z`, `z ∈ p^n log_p(O_k^×)` if and only if `n < ord(z)`.

以及 log-shell 与 `A(k)`（`tex:87–89`）：`A(k)` 是“`Q_p`-linear automorphisms of `k` that map `log_p(O_k^×)` onto itself, equivalently the log-shell `p^{-1} log_p(O_k^×)`”（引 III Rem.1.2.2(i) p.36）。我们自己的笔记：`round2-source-audit.md:40`（“`I_v = p⁻¹ log_p(O_v^×)`（本例 p 为奇素数）是 log-shell”）、`:41`（`A(k_v)` 的定义，并明说“不应直接定义为真实 Ism”）。LP1 把判别式与它的**上限**写清（`round3-semantic-audit.md:218–239`）：由全部整数 `n` 的 membership profile 只能恢复 `ceil(ord_p(Tz)) = ceil(ord_p(z))`（`:236`），“它一般不恢复 `ord_p(Tz)=ord_p(z)`”（`:239`）。RI-06 列出缺失对象（`round3-realization-obligations.md:97–107`）：整数环、极大理想、**p-adic logarithm**、`ord_p(p)=1` 的归一化、value group `(1/e)Z`、以及 `e_v` 的证明。

**2) 最小形式化内容。** 一个有限扩张 `k/Q_p`，其整数环 `O_k`、素元 `p`、归一化 `ord_p(p) = 1`（于是 value group 是 `(1/e)Z`）；乘群 `O_k^×`；`p`-adic logarithm（收敛幂级数）作为从 `O_k^×`（`p` 奇、`e ≤ p−2` 时）到加法群 `k` 的同态；它的像 `L = log_p(O_k^×) ⊆ k`，是一个 `Z_p`-格；log-shell `p^{-1}L`。`Lean` 需要的数据：带显式 `e` 的 `Valued`/局部域结构、打包成结构的 log 级数、以及像的身份等式。

**3) 最近的形式化对象（本清单最强的一处匹配）。** `LocalFieldAudit.Filtration.integerIdealImage p 1`（`Z_p` 的极大理想的一次幂在 `Q_p` 中的像，即 `p·Z_p = {ord ≥ 1}`）配合

`LocalFieldAudit.Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation : x ∈ p^n • integerIdealImage p 1 ↔ n < x.valuation`

——这**逐字**就是上文 `(1.2)` 的判别式 `z ∈ p^n log_p(O^×) ↔ n < ord(z)`，只不过 `L` 是极大理想而不是对数像。另有 `Filtration.integerIdealImage_eq_pow_ball`、`preserves_maximalIdealImage_iff_ball`、`preserves_ball_valuation`，`Shell.scalar_layer_membership_iff`、`Shell.padic_threshold_iff`（**假定** measurement/layer 对应，见其签名里显式的 `hmeasure`），`ScaleLedger.layer` / `layer_image_shift` / `existsUnique_layer_of_auto`。

**4) 精确 gap（这一行的 gap 比“缺 log”更细，值得单列）。** 在基域 `k = Q_p`，`e = 1`，所以集合 `{ord ≥ 1/e} = {ord ≥ 1} = m`，**层算术已经证完**；缺的只有两件事：(i) **出处**——该集合是对数像（`log_p(O^×) = m` 的证明），它带来 `log(zz') = log z + log z'`，也就是让 `A(k)` 真正作用在壳上并保持乘法的那个性质；(ii) **分歧情形**——`e_v = 105, 35` 时 `1/e_v ≠ 1`，集合就不是 `m`。分类：[blocked-by-missing-library: p-adic logarithm]（出处与分歧情形）＋[needs-real-arithmetic-data]（`e_v`、`k_v`）。层成员资格那一半是 [definition-only] 且已在本仓库基域完成。

**5) 假装会怎样。** 若把 `L := integerIdealImage p 1` 直接叫 `log_p(O^×)`，就把一个 `Z_p`-格（极大理想，`ord ≥ 1`）与对数像等同一个东西；在分歧 `k_v` 里会整体错开 `1/e_v` 一整层，于是 RI-07 想要的 valuation 界、以及 `p²R̃ ⊆ hull` 都会是关于**错格**的命题。代价可量化：短文那两个数相距 `2 − 97/35 = 27/35` 个 `log p`，小于一个 `log p`——错一层就足以翻转结论。

### D05 Θ-link

**1) 来源记录：E4 —— definition not in local evidence。** 直接证据是 `GAP.md:9`：模型“没有定义 Hodge theater、实际 Θ-link、tensor packet 或 log-volume”。补充笔记 `core-and-bridges.md:9`（**补充，非本轮主材料**）只给负向刻画：“Θ-link 只粘合指定的 Frobenioid 部分，并不提供跨副本的环同构”；`:21` 记“log-theta-lattice 的横箭头是 Θ-link 版本，纵箭头是由局部对数构造的 log-link；全格不能先验视作交换方格”；`:40` 把“逐一确定各版 Θ-link 实际提供的单子、Galois 作用及图表”列为桥接义务。形式化侧也有同样的自陈：`bridge/IUTBridge/Slots.lean:28–30` “There is no IUT packet, no Kummer isomorphism, no seed region and no Theta-link here”。**没有任何笔记记录它的定义**（定义域、值域、粘合的是哪份子数据、`1/(2ℓ)` 次根与标签约定等）。按纪律：不重建。

**2) 最小形式化内容（此处的“最小内容”本身就是 gap 说明，不是对原文的断言）。** 若要在 Lean 里**至少能陈述**它，需要：两个 theater 作为同时携带“Frobenioid/单子部分”与“环部分”的结构；一个只在前者上给出同构、对后者不给任何关系的 link 对象；并显式禁止“整体类型的双射”。也就是说它的形式内容是一个**带两个投影的结构 + 仅在遗忘像上的同构**，而**不是**环境类型间的双射。

**3) 最近的形式化对象。** 没有同构物。形态上最近的是 `IUTAudit.Transport.Reindexing`（显式 forward/inverse + 两条逆律）与其上的 `transport_projection`、`rho_follows_place`——但它是**反面**形状：`Reindexing` 是标签集之间的双射，而 Θ-link 恰恰不是集合论传输（`round3-semantic-audit.md:198` 记 III Rem.3.11.1(iv) 的 APT 警告正是指这一点）。`Orbit.unionOfImages` 与本行无关。

**4) 精确 gap。** [definition-only]，而且比“缺一个定理”更糟：**我们连缺什么都无法精确陈述**。三个索引（stage `j`、tensor slot `i`、place `v_i`）在 `round2-source-audit.md:53–57` 有清楚记录，link 本身没有。

**5) 假装会怎样。** 若用 `Reindexing`（或任何双射）建模 Θ-link，就把 link 变成两个 theater 环结构的集合论等同——正是 APT 禁止的那一步——并让环层面的事实可跨 theater 搬运，等于用定义**顺便**证明了整套理论里最关键、也最受质疑的那一步。

### D06 holomorphic hull

**1) 来源记录（E2：有刻画，缺最小性类）。** `round2-source-audit.md:165` 记 III Rem.3.9.5(i) p.127 的 hull 定义得到候选后果：

> hull 是包含 U 的最小 λ₀·O 型区域，或在非 relatively compact 情况下为整个 packet。

同笔记 `:150–157` 把四个积分结构分开（全纯 packet 的环整数结构 `O`；mono-analytic log-shell 的张量格 `I`；`L = ⊗ log_p(O_i^×)`；`R̃ = normalization(⊗ O_i)`），`:162` 记 `M_{v⃗} = p^{floor(λ−d_I−a_I)−b_I} R̃_{v⃗}`。`round3-realization-obligations.md:127` 记 RI-08 的来源链（III Rem.3.9.5(i) p.127；IV Props.1.1–1.4 pp.9–13；Step(iv),(v) pp.26–28）。`controversies.md:18` 记 Θ 侧数值是“不定性下可能像之并的 holomorphic hull 的 log-volume，允许先验取 +∞”。短文（二次文献）给两支（`tex:386–389`）：若 `U_j` 非 relatively compact，hull = 整个 packet（log-volume `+∞`）；否则 hull `= η·O`，`η` 各分量非零。

**2) 最小形式化内容。** 环境空间 `V`（`Q_p`-向量空间或有限个域的积）＋一个选定的 `Z_p`-order `O ⊆ V`；区域族 `H = {λ·O : λ ∈ k^×} ∪ {V}`（“`λ₀·O` 型区域”）；`hull U := H` 中包含 `U` 的最小元（存在时），两支由 `U` 是否有界决定。还需要 `O = R̃` 的识别与 log-volume（格上的测度，归一化 `μlog(R̃)=0`、`μlog(pR̃) = −log p`）。

**3) 最近的形式化对象。** `IUTAudit.Orbit.orbitEnvelope`＋`envelope_minimal`（“任何包含全部允许像的界都包含包络”）＋`envelope_minimal_closed`＋`envelope_idempotent`；`IUTAudit.Scale.no_uniform_bound` 可当作 `+∞` 支的离散玩具。

**4) 精确 gap。** `orbitEnvelope` 的最小性是对**全部谓词** `V : X → Prop` 取的（于是最小者就是并本身）；hull 的最小性是对**受限的 `O`-模区域类**取的。没有这个限制，包络不是 hull。缺：类 `H`、`O = R̃`、log-volume、两支判据。[definition-only]（`H` 与最小性，现在就能写）＋[blocked-by-missing-library: `⊗O_{k_i}` 的归一化 `R̃`]＋[needs-real-arithmetic-data: `λ, d_I, a_I, b_I`]。

**5) 假装会怎样。** 若令 hull `:= orbitEnvelope`，hull 就变成“包含全部像的最小集合”，也就是并本身，它的 log-volume 既不能从 `p²R̃ ⊆ ·` 得到 `≥ −2 log p` 的下界（因为不是 `R̃`-模），Step (v) 的 `M_{v⃗}` 上界也不再适用于它；反过来若允许“任何包含 `U` 的区域”叫 hull，取大就破坏上界——**hull 会从包络退化成定义**，`−2 log p` 与 `−97/35 log p` 的分离就只是两个我们自选集合的体积比较。

### D07 mono-analytic vs holomorphic structure

**1) 来源记录（E3：角色记录，定义缺）。** `round3-realization-obligations.md:41` 把“**holomorphic 与 mono-analytic 的有限空间及 lattices**、局部 `κ_c`、direct-sum/tensor construction、选定坐标 `ι_hol`、`ι_an`”整体列为 RI-02 的**缺失对象**。`round3-semantic-audit.md:90–100` 只给义务的**形状**（`W_hol(m,i,v), W_an(i,v)` 两个有限 `Q_p`-空间、`L_hol ⊆ W_hol`、`L_an ⊆ W_an`、`ι_hol`、`ι_an`、只对 actual `c` 的 `κ_c`），并且这三条是“需要实际构造以下类型”的待办，不是定义。分层依据记录在 `round2-source-audit.md:91`（M4 行）、`:154–157`（全纯 `O` 用 III Prop.3.1(ii)；mono-analytic 张量格 `I` 用 III Prop.3.2(ii)）。补充笔记 `round5-joint-realization.md:153` 给出更清楚的分层（III Fig.3.6, p.176）：local LGP-monoids／`F_mod` 的 copies 需要 mono-analytic containers，其 Kummer theory 与 Ind1/Ind2 **不兼容**；étale theta function／κ-coric 几何结构那一层独立于这些 containers。

**2) 最小形式化内容。** **两个不同的类型** `W_hol`、`W_an`，各自带自己的格，各自带一个到同一个 `k_v` 的坐标同构，中间由 `κ_c` 相连；并且必须显式记录“`κ_c` **不是**环结构的同构”。数学内容就是：同一个 `Q_p`-向量空间承载两个不同的环/格结构，二者之间的桥是某个特定 orbit 里的 Kummer 同构，不是环同构。

**3) 最近的形式化对象。** **没有对象承载两个结构**。最接近的是“同一类型上的两个作用”：`IUTBridge.Slots.Tuple` 上的 `relabel`（标签）与 `slotwise`（标量），以及 `Slots.relabel_slotwise`/`slotwise_commutes_of_invariant` 关于二者不相交换的判据；再有 `LocalFieldAudit.Shell.image_scalar_layer` 被用两次。`Transport.Reindexing` 有显式 forward/inverse——那是货真价实的同构，正是 link **不该**有的东西。

**4) 精确 gap。** [definition-only]，且缺的那一半是**负向内容**：一条“`κ_c` 不保环/不保乘法”的记录。没有两个类型，就无从证明这一点——今天所有相关对象都活在**同一个**类型上：`Shell` 的 `V` 是任意 `K`-模，但本文关心的实例全部取 `K = ℚ_[p]`（`Slots.Tuple`、`Filtration.ball`、`ScaleLedger.layer` 直接就是 `ℚ_[p]`）。

**5) 假装会怎样。** 把 holomorphic 与 mono-analytic 折叠成同一个类型（当前所有 Lean 的默认状态），等于让环结构自动跨 link 搬运：在一边证明的 `log_p(O^×)`-保持会在另一边免费成立。这正是让 IV Step (v) 的“任意线性自同构”估计能覆盖到来源只允许 `Ism`/`κ` 的地方的那一步——也就是 `round3-realization-obligations.md:18` 禁止的“把 κ 的边缘允许性和 σ 的边缘允许性拼成联合允许性”的同型错误。

### D08 tensor / packet construction

**1) 来源记录。** 结构是 **E1**（`round2-source-audit.md:43–51`）：`P_j = ⊗_{i∈J} (⊕_{v∈E} k_v) ≅ ⊕_{v⃗∈E^J} k_{v⃗}`，`k_{v⃗} = ⊗_i k_{v_i}`，`pr_{v⃗} : P_j → k_{v⃗}`；并强调三个索引必须一直分开：stage `j`、tensor slot `i`、place `v_i`（`:53–57`）。短文（二次文献）给 `k_I = ⊗_i k_i`、`R_I = ⊗_i O_{k_i}`、`log_p(R_I^×) = ⊗_i log_p(O_{k_i}^×)`、`dd_I`、`R̃_I = normalization of R_I`，并记 `k_I` 是有限个域 `L` 的积、`R̃_I` 是它们整数环的积（`tex:71–78`）；packet 是“over the labels `S_j` 的 tensor product of the direct sum over places”（`tex:99–105`）。归一化一侧是 **E2**：`round3-realization-obligations.md:129` 把“实际 finite tensor packet 的 simple-field decomposition、`R̃ = normalization(⊗O_i)`、tuple projection、相容 log-volume 归一化”列为缺失对象；`round3-semantic-audit.md:284–286` 记 different 只出现在“从 tensor of integer rings 到其 normalization”的比较与 hull 界里。

**2) 最小形式化内容。** 有限索引集 `I = {0..j}` 与有限 place 集 `E`；`Q_p`-空间 `⊗_{i∈I}(⊕_{v∈E} k_v)`；按元组 `v⃗ ∈ E^I` 的直和分解与投影 `pr_{v⃗}`；`Z_p`-格 `⊗_i O_{k_{v_i}}` 及其归一化 `R̃`（简单因子整数环的积）；以及三索引纪律（stage／slot／place）。

**3) 最近的形式化对象。** `IUTBridge.Slots.Tuple p n`（`Fin n → ℚ_[p]`）——它是**积**，`n` 份**同一个**域；`IUTBridge.WeightedLedger.weightedLedger`（`Σ_j w_j · v(x_j)`，与其上的 `weightedLedger_invariant_iff`、`norm_prod_eq_zpow_totalLedger`）；`IUTBridge.Slots.relabel`/`slotwise`/`swap23`。

**4) 精确 gap。** 四条：(a) 积 ≠ 张量积，`k_{v_i}` 是**互不相同**的域，不是 `n` 份 `ℚ_p`；(b) 没有对 place 的直和，于是没有“按元组的投影”`pr_{v⃗}`；(c) 没有整数环与归一化 `R̃`，于是没有纯张量上的 valuation 加性——`LocalNumerics.transformed_sum_excludes_cut` 里那个和是**被假定的整数和**，其 docstring 自己说 “The sum is just an integer sum, not an asserted tensor valuation”（`IUTAudit/LocalNumerics.lean:81–82`）；(d) 三索引纪律只部分存在（`LocalNumerics.Place`、`rhoNumerator`）。分类：[blocked-by-missing-library: `⊗O_{k_i}` 的归一化]＋[needs-real-arithmetic-data: 次数 105／35 的 `k_{v_i}`]。

**5) 假装会怎样。** 若把 `Fin n → ℚ_p` 当 packet，会同时犯两个错：(i) 所有 tensor slot 承载**同一个域**，于是 `σ_*` 退化成同一根纤维上的置换（`round2-source-audit.md:138` 记待证的正是“来源同步”，在这种情况下它变成自动的），(ii) `weightedLedger` 可被读成张量 valuation，把一个**假定**的整数恒等式升级成“packet 上的 valuation 加性”——那正是 M4/T3 未证的桥。

### D09 Ind1–Ind3 允许操作

**1) 来源记录（E1）。** `round3-semantic-audit.md:11`：

> **Ind3 不应硬塞进群作用。** IUT III Theorem 3.11(ii), p.156 把它描述为随 vertical parameter m 变化的 upper-semi-compatible inclusions/surjections。

同笔记 `:114–121` 给三层级（Kummer unit data = II Def.4.9(i) p.154；固定 procession 的 Ind1/Ind2 = III Thm.3.11(i) p.154；不同 radial presentations 之间 = II Example 1.7 pp.32–35），`:140–152` 给“不能把 Ind3 当作自动可逆的群作用”以及最低的闭包写法 `∀ c, Adm(c) → ∀ a, Allowed12(a,c) → ∃ c', Adm(c') ∧ T_a(out c) ⊆ out c'`，并明说 `Allowed12` 不能直接取成全部 `A(k)` 矩阵。`round2-source-audit.md:110–114` 给 T1–T5 表；短文（二次文献）给 Ind1 的机制（`tex:328–336`）：procession 的态射 = stages 的保序单射 + 每个 stage 的 capsule-full poly-morphism，**stage 之间没有条件**（IUT I Def.4.10 p.120）；Ind1 是 procession 自同构诱导的不定性，Ind2 是“independent copies of `Ism` on the direct summands of the factors”（III Thm.3.11(i) p.154）。

**2) 最小形式化内容。** 一族**允许操作**，其中操作是**关系**而不是函数：Ind1 = procession 的自同构（每个 stage 的 capsule-full poly-isomorphism，index set 的置换）；Ind2 = `Ism` 在每个 factor 的每个 place-summand 上独立作用；Ind3 = 依赖 `m` 的、**有向不可逆**的包含/满射。外加联合允许谓词 `Adm(c)` 与投影方程 `pr_w ∘ R_a = (⊗_i ψ_i) ∘ σ_* ∘ pr_u`。

**3) 最近的形式化对象。** Ind1 玩具：`IUTBridge.Slots.relabel` ＋ `relabel_slotwise`（投影方程的玩具版）＋ `slotwise_commutes_of_invariant` ＋ `mixingEquiv_commutes_swap`（一个**确实**等变的混槽自同构——它存在的意义正是防止把对角判据当全部，见 `Slots.lean:129–134`）。闭包：`IUTAudit.Orbit.IsClosed`、`CompositionClosed`、`HasIdentity`、`envelope_closed`（闭包是**假设**）。联合数据与来源追踪：`IUTAudit.Transport.SeededFamily`、`Reindexing`/`transport_projection`/`rho_follows_place`。具体 `p`-adic 联合关系：`IUTBridge.Admissibility.marginals_do_not_force_joint`。

**4) 精确 gap。** (a) `Equiv.Perm` 与函数强制**双射与全定义**，Ind3 两者都不是，模型必须换成关系/有向图 —— [definition-only]；(b) 没有 procession、capsule、stage 结构，`Slots` 只有单 stage 的标签置换，因此**根本没有 Ind1** —— [definition-only]；(c) `CompositionClosed` 是假设而非导出，而这正是 T5/RI-05 的核心 —— [needs-real-arithmetic-data]；(d) `ψ_i ∈ A(k_{w_i})` 与实际 `Ism` 的差距见 D01。**不是** library 缺口：关系、有向图、groupoid 在 Mathlib 里都有现成语言。

**5) 假装会怎样。** 若拿 `relabel` 当 Ind1、拿 `Orbit.IsClosed` 当 `U_j` 的闭包，Ind1 就成了可逆标签置换、Ind3 就成了群作用；于是“轨道封闭”由一条来源不支持的假设推出，而 Step (v) 那条异议（某个置换像**离开**容器）会在结构上被**消隐**——封闭的轨道不可能离开。

### D10 splitting monoid generator θ

**1) 来源记录（关系 E1／元素 E2）。** 短文（二次文献）`tex:283–285`：`θ ∈ k_{v_j}` 是 splitting monoid 在 `v_j` 处 label `j` 分量的生成元，即 theta 值 `q_{v_j}^{j²}` 模一个单位根（引 III p.11），故 `ord(θ) = j²ρ(v_j)`。我们的笔记：`round2-source-audit.md:88`（M1 行）记“IUT III p.11 把 splitting-monoid generators 与 `q̂_v` 的 `j²` 次幂联系”，并指出“在具体有限完成域内构造 θ，连同 root-of-unity、field-of-definition 与估值证明”仍是短文额外完成的解释；`round3-realization-obligations.md:55` 把“splitting generator `θ` 的域定义与 root-of-unity 选择”列为缺失对象。补充：`round5-joint-realization.md:136,138` 记 Def.3.8(i) 的 pilot 由 generators up to torsion 决定，III Rem.3.11.4(i) p.171 采用 roots-of-unity orbits 而非指定元素。

**2) 最小形式化内容。** 一个具体有限扩张 `k_v`（此处 `Q_p` 上次数 105 或 35）中的元素 `θ`，取作指定 `q̂_v` 的 `j²` 次根，连同：定义域、单位根不定性（`μ_{2ℓ}` 的 torsor，且必须证明它在 `k_v` 内）、以及估值 `ord(θ) = j²ρ(v_j)`，其中 `ρ(v) = ord_p(q̂_v)`（短文 `tex:273–274` 给 `ρ(v) = m/14`，故落在 `(1/14)Z`）。

**3) 最近的形式化对象。** `IUTAudit.LocalNumerics.rhoNumerator`（`Place` 上取整数值，单位 `1/7`）＋ `swap23_rho_positions`（证明“用错槽位会差 5/7”）＋ `sourceTuple`/`targetTuple`/`swap23_tuple_and_theta`；基域侧的乘性对照是 `IUTBridge.WeightedLedger.norm_prod_eq_zpow_totalLedger`（范数之积 = `p^{−ledger}`，即短文 `(1.1)` 的基域类比）。

**4) 精确 gap。** 我们手上是“挂在**标签**上的一个整数”，对象是“**次数 105 的域**里的一个元素”。缺：域、元素、单位根 orbit、`ord(θ)=j²ρ`。分类：[needs-real-arithmetic-data]（主）；构造 `K_v = k_0(E_0[105])` 超出本仓库范围，故也带一点 [blocked-by-missing-library]（分歧扩张与 `μ_n` 的具体构造；Mathlib 有 `NumberTheory.LocalField.Basic`，但没有这条具体扩张路径）。`LocalNumerics` 自己的 docstring 已声明它不建立 “membership in the IUT pilot region, or the Ind1 action”（`IUTAudit/LocalNumerics.lean:9–11`）。

**5) 假装会怎样。** 若把 `rhoNumerator` 读成“`ord_p(θ)` 的值”，整条 Step (v) 链条就在用“我们定义成 `9·(1/7)` 的那个整数”做论证；`107/35 > 2` 这类数值分离（`repaired_cut_and_cost`、`local_integer_checks`）就变成关于我们自己常数的真命题——用定义法**顺便**证成了关于 IUT 的断言。

---

## 3. 缺口分布

| 类别 | 涉及对象 | 缺的具体东西 |
|---|---|---|
| **[definition-only]** | D01(a)(b)、D02、D03(region 谓词)、D05、D06(定义层)、D07、D08(b)(c 部分)、D09 | ind-模与 `G` 作用、`H`-族、`Adm`/`out`、Θ-link、`H` 与最小性、两个结构类型、place 直和与 `pr_{v⃗}`、关系型操作 |
| **[needs-real-arithmetic-data]** | D01(c)(d)、D02、D03、D04(ii)、D06、D08、D10 | 次数 105／35 的 `k_v`、`e_v`、`q̂_v`、`θ`、`λ, d_I, a_I, b_I`、实际 `κ_c` 与 `out(c)` |
| **[blocked-by-missing-library]** | D04 与 D01(c)（**p-adic logarithm**）；D06 与 D08（`⊗O_{k_i}` 的**归一化 `R̃`**）；D10（分歧扩张／`μ_n` 的构造，次要） | 见左。仓库侧证据：`GAP.md:40`、`round3-realization-obligations.md:99` 都把 p-adic logarithm 列为缺失对象；`research/round3-source-cache/manifest.json` 等三份 manifest 固定的 Mathlib 缓存（13 个模块，commit `85e3a25e…`）里没有任何 logarithm 模块。 |

一句话：**三类缺口没有互相替代关系**。把 [definition-only] 写成结构字段不会消掉 [needs-real-arithmetic-data]；反过来，拿到 `e_v` 与 `k_v` 也补不上 Θ-link 的定义。

---

## 4. 最值得先形式化的三个对象

按“可行性 × 收益”排序，且**明确标注依赖**：

1. **D04 log-shell / `log_p(O^×)`（先做未被 log 阻塞的那一半）。**
   可行性高：集合层面的判别式 `x ∈ p^n·m ↔ n < ord(x)` 已由 `LocalFieldAudit.Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation` 在基域证完，缺的是“这个格是**对数像**”与分歧情形。收益高：它是 RI-06 → RI-07（`ceil` 界与逐因子 valuation 上界）的主要入口，也是 D01(c) 的必要条件。
   **这一项正是被缺失的 p-adic logarithm 阻塞的**：出处 `log_p(O_k^×) = m_k`、乘性 `log(zz')=log z + log z'`、以及 `e_v = 105,35` 的 `1/e_v ≠ 1` 三项都需要它。因此下一步的正确切法是：先把 `L` 的层结构与 `PreservesLayers → ceil` 的桥（`IUTAudit.LocalNumerics.PreservesLayers`、`layer_preserves_upper`）接到已有 `Filtration` 定理上，把 log 当作**显式参数**传入；不要先造一个叫 `log` 的字段。

2. **D09 Ind1–Ind3 写成关系型允许操作 + 投影方程。**
   可行性最高：无 library 阻塞（关系、有向图、`Rel` 都在），`Slots.relabel_slotwise` 已经是投影方程的玩具版，`Orbit` 的 `IsClosed`/`CompositionClosed`/`envelope_closed` 已有闭包骨架。收益：这条直接对着 G03 的 T3/T5，是 `round3-realization-obligations.md:93` 标为“当前优先审计”的语义桥梁的另一半。
   关键设计约束（否则做了也没用）：`Ind3` 必须是**关系**（不可逆、非全定义），`Allowed12` 不得取成全部 `A(k)` 矩阵，`CompositionClosed` 必须是待证目标而不是假设。

3. **D02 的 `SeededFamily` 实例化（possible-images family 的可调用骨架）。**
   可行性中：`IUTAudit.Transport.SeededFamily` 五个字段的形状已经对，缺的是真实数据；先在**一个** `c`（固定 `m`、Ind2 取恒等、不调 Ind3）上实例化，就能把 `familyImage` 变成可检验目标。收益：一次实例化同时压住 D03 与 D05 的语义漂移（region 与 union 都不能再随手定义）。
   依赖：D03 的域与理想数据（或至少其**参数化**版本，并显式标注条件式）。

**被排除但值得记录**：D06（holomorphic hull）是**收益最高**的一项（它把一切变成一个数值断言，且是 Step (v) 的落点），但它同时依赖 `R̃` 的归一化（[blocked-by-missing-library]）与 D02/D08 的数据，因此**不该排进下一步**；先把它的**定义层**（区域类 `H` 与最小性）写出来即可，不必等 `R̃`。

---

## 5. 最危险的单个假桥

**把 `ℚ_p ≃ₗ ℚ_p`（或 `A(k)`）读成 `Ism` 元素。**

理由不是它最“远”，而是它最**近且已证**：`LocalFieldAudit.Filtration`／`Shell`／`ContinuousLinearity`／`ScaleLedger`／`Admissibility` 里几十条定理都是真定理、无 `sorry`、公理依赖可查，一旦有人在散文里写“`Ism` 是保壳的 `Q_p`-线性自同构，而我们的 `e` 就是这样的自同构”，读者会以为那句“于是”已由 Lean 覆盖。实际上被覆盖的只是一个**单域、无 `G` 作用、单格**的自同构，而 `Ism` 是**带 `G` 作用的 ind-模上对全部 open-`H` 格的相容族**（D01）。后果是具体的：它同时抹掉 `round3-semantic-audit.md:55` 的“像 vs 全部不变量”，把 `A(k)` 的**过度近似**性质（`round2-source-audit.md:41` 明说“不应直接定义为真实 Ism”）变成等同，于是“对每个 `ψ ∈ A(k)` 都不包含”那类论证会被听成“对每个真实 `Ism` 元素都不包含”——而这正是 Urahigashi 短文与 IUT 之间尚未裁决的那一步。

次危险两项（记录在案，但不如上一条近）：`mono-analytic ≡ holomorphic`（D07，会让环结构跨 link 自由搬运）；Θ-link `≈ Reindexing`（D05，会用定义法给出 APT 明确禁止的传输）。

---

## 6. 本文件的可失败判据

- 若某行说的“最近的现有形式化对象”其实**满足**该对象所需的全部条件（例如有人给出 `Ism` 的真实 ind-模实例并证到 `L_H` 族），该行的 gap 判定即失效，须改写。
- 若 `round3-semantic-audit.md:128–138` 之后已有新笔记抽出 `Adm(c)`/`out(c)` 的具体类型，D02 的 E3 应升级为 E1，本文件相应行作废。
- 若发现任一引用行号对不上（笔记被改动），以笔记现行为准，本文件作废重写。
- 若 `GAP.md:9` 关于 Θ-link 未定义的记录被后续轮次推翻（即写出定义），D05 的 E4 须降级；在推翻之前，本文件的 E4 是**唯一**诚实标法。

## 7. 本轮做了什么、没做什么

- **做了**：读 `research/round3-semantic-audit.md`、`round3-realization-obligations.md`、`round2-source-audit.md`、`controversies.md`、`sources.json`、`GAP.md` 全文；读本地缓存批评短文 `urahigashi-v0.8.0.tex` 全文（§1–§5）；读 `bridge/IUTBridge/*.lean`、`IUTAudit/*.lean`、`local-field/LocalFieldAudit/*.lean` 的声明与模块说明；用 grep 逐一验证本文件引用的 **70 个** Lean id 全部存在（0 缺失）。
- **补充引用**：`research/core-and-bridges.md`、`research/round5-joint-realization.md` 不在本轮指定主材料内，凡用到都标了“补充”；它们只被用来记录**角色/分层**，没有承担任何对象定义。
- **一次抽查（不是引用）**：为确认 `round3-semantic-audit.md:9` 对 `Ism` 的记录没有走样，我在本地已登记字节的 IUT II 缓存文本里比对了 Example 1.8(iv) 那一段，措辞（`G`-等变、ind-topological 模、对每个 open `H` 保持 `O×(G)^H` 的像给出的 lattice）与笔记一致。**该缓存文本不作为本文件的引用来源**：本文件不新增望月原文页码引用，页面级 locator 一律以笔记所记为准。
- **没做**：无网络访问；未构建、未运行 Lean；未修改任何 Lean/验证器/`audit/` 文件；未触碰 `handoffs/`；未引入任何未经笔记记录的原文页码；未把任何来源立场当作本项目已认证的数学结论。
- 本文件不关闭 G01/G03，不认证 `Cor.3.12`、Theorem 1.10 或 abc，也不认证短文 §4 的两条引理。
