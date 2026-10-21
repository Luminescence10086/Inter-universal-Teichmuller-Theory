# 语义对应台账：形式对象 ↔ 真实接口义务

日期：2026-10-21。分支 `explore/correspondence`（base `c1fa0cc`）。
机器版：`bridges/correspondence.json`（由 `python -B bridges/correspondence_gen.py` 生成）；
生成器会把每个 `formal` 锚点拿去与三套工程**已导出**的定理清单比对，缺一即报错。

配套证据：`research/exploration/definitions-inventory.md`（源语义清单，逐条记到笔记行号，
并给 E1–E4 证据分级；70 个 Lean id 已核对存在）与
`research/exploration/log-kummer-feasibility.md`（库级可达性，见下文）。

**这份台账不证明任何 IUT 命题。** 它做三件事：把每个形式对象钉到具体义务（RI-01…RI-08）
上；写清它证明了什么、缺什么、什么情形会推翻这条对应；给出尚为候选的三个结果。
任何新定理若不能归入某条的 `proves` 或 `gap`，就应当新增条目而不是归功于既有条目。

## 状态词汇

| 状态 | 含义 |
|---|---|
| `exact-base-field-theorem` | 在实际 `Q_p` 上有完整证明，但只谈基域对象，不是 IUT 对象 |
| `toy-coordinate-shadow` | 在坐标/槽位层面忠实，真实对象缺席（能"投影"，不能"实例化"） |
| `conditional-interface-only` | 只给出"若缺对象存在则结论成立"的形状，缺对象是假设 |
| `toy-generic-container` | 任意集合上的容器机制，尚未证明它是真实族 |
| `blocked-by-missing-log` | 真正的缺口是 `log_p` 的像；本 pin 无该接口（见可行性报告） |

## 八个条目

| id | 义务 | 形式对象（定理） | 状态 | 缺什么 |
|---|---|---|---|---|
| C-01 | RI-04 | `Slots.relabel_slotwise`、`slotwise_commutes_of_invariant`、`swap23_exchanges_high_slots`、`LocalNumerics.swap23_tuple_and_theta` | toy-coordinate-shadow | 无 Hodge theater、无 G/H；标号作用不是 Ind1 procession |
| C-02 | RI-07 | `WeightedLedger.weightedLedger_slotwise`、`weightedLedger_invariant_iff`、`Integration.weightedLedger_combined_invariant_iff`、`Scale.weighted_comparison_forces_bound` | exact-base-field-theorem | 权重是任意整数，未与 log-volume 权重认同 |
| C-03 | RI-01 | `Admissibility.not_rectangular_of_graph`、`rectangular_subrelation_freezes_layer`、`marginals_do_not_force_joint`、`Transport.rectangular_iff_product` | conditional-interface-only | 无 Ism、无 open-H 格族、无 Kummer 元素 |
| C-04 | RI-06 | `ScaleLedger.mem_layer_iff_le_valuation`、`layer_image_shift`、`valuation_shift`、`Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation` | blocked-by-missing-log | 左边对象 `log_p(O^×)` 未构造 |
| C-05 | RI-01 | `ContinuousLinearity.map_padic_smul`、`preserves_integerIdealImages` | exact-base-field-theorem | 真实限制映射未构造 |
| C-06 | RI-05 | `Orbit.envelope_minimal`、`envelope_minimal_closed`、`envelope_covers` | toy-generic-container | 未认同为真实 `U_j`；扩大容器的代价未控 |
| C-07 | RI-08 | `Admissibility.frozen_isRectangular` | toy-coordinate-shadow | 无 normalization、无 tensor packet、无 log-volume |
| C-08 | RI-06 | `ScaleLedger.cost_exact`、`norm_shift` | blocked-by-missing-log | 只有指数恒等式，未定义测度 |

## 逐条要点

**C-01（槽位/标号）** 证明的是：重标把逐槽标量族共轭过去，`swap 2↔3` 恰好换掉高档位。
缺口是对象本身：真实标号作用来自 procession automorphism，而不是 `Equiv.Perm (Fin n)`。
可失败判据：若真实 procession 不是逐槽作用，共轭公式不适用。

**C-02（加权账本）** 这是台账里最强的一条：账本在逐槽标量下**恰**平移 `Σ_j w_j·v(a_j)`；
对一切元组 `σ`-不变 ⟺ 权重向量 `σ`-不变；`Integration` 把"重标+缩放"合成后仍是充要判据。
缺口：权重是手选整数；没有任何东西把它们识别为 log-volume 权重，元素是 `Q_p` 标量而非
Kummer 数据。**它支持"记账"，不支持"体积不等式"。**

**C-03（联合可容许性）** 这是唯一直接谈"κ 与 σ 能否分别验"的条目：当联合关系是图且出现
两个以上取值时，边际可容许性拼不出联合见证；任何矩形子关系都把层冻结。
缺口：关系建立在"`Q_p` 线性自同构 × 单位球层"上，没有 Ism 群与 open-H 格族。
可失败判据：若真实允许族是乘积状（两个选择独立），这套障碍对它不适用。

**C-04（层判别）** 基域上"理想像的层"与"估值阈值"可双向互换，这是 `p^n log_p(O^×)`
判别式的**右侧**。左侧（`log_p` 的像）不存在，所以真实等价式没有写出来。
低分歧（`e ≤ p−2`）时 `log_p(O^×)` 可能严格小于极大理想，届时必须改用带 `a,b` 误差的
sandwich —— 这正是不能把 C-04 直接当 RI-06 的原因。

**C-05（线性性）** 连续加法映射到 `Q_p` 即自动 `Q_p`-线性：这把 RI-01 里"限制落在 `A(k)`"
的一个子条件（线性性）从义务清单里划掉了，但限制映射本身仍未构造。

**C-06（容器）** 任意集合上的最小闭容器与幂等性。风险是把它当成真实 `U_j`：扩大容器只有在
额外代价受控时才算修补，本轮不做这件事。

**C-07（冻结层）** 冻结层后独立边际推理才成立；这是 C-03 的正面版本。它描述的是"层必须被
钉住"这一必要条件，而不是真实 hull 的归一化。

**C-08（层搬运）** `cost_exact` 只是集合像与带符号指数差；**没有**测度、体积或最优价格。
`norm_shift` 是元素范数的缩放，不是测度的缩放。

## 三个候选结果（不在本检出的导出里，故不作锚点）

| id | 产出 | 价值 | 缺口 |
|---|---|---|---|
| K-01 | `candidates/restricted-ledger`（RI-07） | 把全空间加权不变性判据化为受限域上**有限个整数等式**（`integer_span_criterion` → `restricted_ledger_criterion`），并给出"受限域保账而权重非全空间不变"的二槽实例 | 真实 admissible region 未构造，`hgen/hreal` 仍是假设 |
| K-02 | `candidates/orbit-quotient`（RI-05） | 包络阈值 = 轨道逐坐标最小、`|B(k)|=p^{Σ(N−k_j)}`、扩大预算为整数指数，并用 2/3/4 把 U 与 H 分开 | 只到 `ZMod(p^N)` 商环；无 normalization/log-volume |
| K-03 | `candidates/pilot-shadow`（RI-03） | `(b₁,b₁,b₂,b₁)` 的估值向量成为真实对象：轨道恰 4 元、包络恒为 `min(v₁,v₂)`、超额恰一个槽位、标号作用移动模式而包络忽略槽位 | 整数代替估值；无 place、无 pilot、无 Θ-link |

## 证据分级（真实对象在本地证据里"记到什么程度"）

| 级别 | 含义 | 本台账条目 |
|---|---|---|
| E1 | 定义已记录且可陈述 | C-01、C-03、C-04、C-05、C-08 |
| E2 | 只有构造定位，没有数据清单 | C-02、C-07 |
| E3 | 作用/角色有记录，定义缺失 | C-06 |
| E4 | 完全缺失，只有否定性刻画 | （Θ-link 本身；不在本台账条目内） |

**没有一条能升到"实例"级**：E1 只说明"我们知道自己缺的对象长什么样"，不说明它已构造。

## 三个必须拒绝的等同（F-01…F-03）

这三条看起来像进展、实际是错误；写出来是为了让后来的claim可被对照检查。

1. **F-01：把我们 `Q_p`-线性 / `A(k)` 自同构当成 `Ism` 元素。** 最危险，因为它**近且已证**：
   数十条真实的基域定理会悄悄变成关于 IUT `Ism` 群的断言，而来源明确承认 `A(k)` 是过度
   近似（`round2-source-audit.md:41`）——"像 vs 全体不变量"的区分会被抹掉
   （`round3-semantic-audit.md:55`）。会被误读的定理：`latticeAdmissible_not_rectangular`、
   `map_padic_smul`、`slotwise_commutes_of_invariant`。
2. **F-02：把 mono-analytic 结构等同 holomorphic 结构。** 来源要求二者分离正是 link 的内容；
   等同掉就把比较变成同义反复。
3. **F-03：把 Θ-link 当成 `Reindexing`/集合论搬运。** APT 明确禁止集合论同一化；
   `Reindexing` 是双射，是**形状错误**，不是"不完整的正确形状"。

## 下一步三个目标（按成本/阻塞排序）

| 排序 | 目标 | 为何先做 | 必须保持 |
|---|---|---|---|
| 1 | Ind1–Ind3 作为**关系值**允许操作 + 投影方程 | 无库级阻塞；玩具投影公式已是 `Slots.relabel_slotwise` | Ind3 是关系而非群作用；`Allowed12` 严格小于全部 `A(k)`；`CompositionClosed` 是要证的目标而非假设 |
| 2 | 为 possible images 实例化 `SeededFamily` | 容器形状已对，只缺一个实际 Kummer 选择 `c` | 不得把族扩大到恰好包含 witness；membership 必须在原 `U_j` |
| 3 | log-shell 的**未阻塞半边** | 基域判别式已是定理；把 log 作为显式参数传入 | log 像的来源仍需 p-adic 对数；小分歧 `e_v=105,35` 时 `1/e_v≠1`，层索引不能整搬 |

## 从"影子"到"实例"还差什么

按当前证据，任何一条要从影子升为实例，都必须同时补上：

1. **真实算术数据**：具体数域/完成域、`p` 与分歧指数、单位群与极大理想（RI-06 前置）；
2. **对象构造**：Ism 限制、有限 H-invariant 模、Kummer 选择 `c`、pilot 的 image-region；
3. **库级缺口**：`log_p` 的像（C-04/C-08 共因，见 `research/exploration/log-kummer-feasibility.md`）；
4. **hull 与体积**：`R̃` 的坐标实现与相容 log-volume（RI-08），而不是再定义一族容器。

只要其中任一项缺席，对应条目就只能停在表中状态；**把状态词从 `toy-*` 改成
`exact-base-field-theorem` 需要新证明，而不是新措辞**。

## 可重现

```powershell
python -B bridges/correspondence_gen.py     # 重新生成并校验全部锚点
```

生成器不会接受未导出的 id：本轮它已当场抓出三处错误（把 `def` 当 `theorem`、命名空间写错、
一个不存在的 id），这正是台账能被机器核对的意义。
