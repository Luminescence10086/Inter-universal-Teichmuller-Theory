# 对象与语义对应：本轮探索成果报告

日期：2026-10-21。分支 `explore/correspondence`。基线 `c1fa0cc`
（= `integration/core` 上的四件套组合点；其祖先是任务基线 `4841271`）。
本轮不新增任何已准入定理，不关闭任何 gap，不构造 IUT 对象。

## 一、这轮要回答的问题

前几轮把可证的东西证成了"基域影子"：`Q_p` 上的层梯、加权账本、槽位共轭、联合可容许性障碍。
这一轮问三个更靠对象层的问题，并三路并行：

1. **这些影子到底对应 IUT 的哪些对象与义务？**（语义路）
2. **要把影子变成实例，缺的是数学还是接口？**（基础设施路）
3. **pilot 的 4 槽模式能不能成为真实算术对象？**（对象路）

三路各自在独立工作树推进，交付后由我**独立复跑**再合并——不采信执行者自述。

## 二、语义对应：8 条对应 + 证据分级（`definitions-inventory.md` → `correspondence.md`）

每条对应必须写明：形式对象（已导出定理 id）→ IUT 对象 → RI 义务 → 证明了什么 →
缺什么 → 什么会推翻这条对应。锚点由 `bridges/correspondence_gen.py` 与三套工程
**已导出的 212 条定理**逐个比对，未导出即报错。

| id | 义务 | 状态 | 关键内容 |
|---|---|---|---|
| C-01 | RI-04 | toy-coordinate-shadow | 重标把逐槽标量族共轭；`swap 2↔3` 恰换高档位 |
| C-02 | RI-07 | exact-base-field-theorem | 账本恰平移 `Σ_j w_j·v(a_j)`；对所有元组不变 ⟺ 权重置换不变 |
| C-03 | RI-01 | conditional-interface-only | 联合关系是图时边际拼不出联合见证；矩形子关系冻结层 |
| C-04 | RI-06 | blocked-by-missing-log | 基域上"理想像层 ↔ 估值阈值"双向成立 |
| C-05 | RI-01 | exact-base-field-theorem | 连续加法映射到 `Q_p` 即自动 `Q_p`-线性 |
| C-06 | RI-05 | toy-generic-container | 最小闭容器存在且幂等 |
| C-07 | RI-08 | toy-coordinate-shadow | 冻结层后独立边际推理才成立 |
| C-08 | RI-06 | blocked-by-missing-log | 层间搬运是带符号指数差的集合恒等式 |

**证据分级**（真实对象在本地证据里"记到什么程度"，逐条引到笔记行号）：

| 级别 | 含义 | 条目 |
|---|---|---|
| E1 | 定义已记录且可陈述 | C-01、C-03、C-04、C-05、C-08 |
| E2 | 只有构造定位，无数据清单 | C-02、C-07 |
| E3 | 角色有记录、定义缺失 | C-06 |
| E4 | 完全缺失，只有否定性刻画 | Θ-link（不在条目内） |

**没有一条能升到"实例"。** E1 只表示"知道缺的对象长什么样"。

## 三、三个必须拒绝的等同（写入台账，机器可查）

| id | 禁止的读法 | 为何危险 |
|---|---|---|
| **F-01** | 我们的 `Q_p`-线性 / `A(k)` 自同构 **就是** `Ism` 元素 | 近且已证：数十条真实基域定理会悄悄变成关于 IUT `Ism` 群的断言，`A(k)` 的"过度近似"地位被抹掉，"像 vs 全体不变量"的区分消失 |
| F-02 | mono-analytic **就是** holomorphic 结构 | 来源要求二者分离正是 link 的内容；等同即同义反复 |
| F-03 | Θ-link **就是** `Reindexing` / 集合论搬运 | APT 明确禁止集合论同一化；`Reindexing` 是双射，属于**形状错误** |

F-01 直接约束本仓库既有 73 条准入的表述：它们是 `A(k)` 层的真实定理，
**不是**关于 Ism 的命题。

## 四、基础设施：只有一处是数学性的（`log-kummer-feasibility.md`）

方法：对固定 Mathlib（`85e3a25e`）做 import 完整探针 + 源码 grep，每条结论对应一行 `#check`。

| 对象 | 判定 | 已有 | 缺 |
|---|---|---|---|
| `ℚ_p^× ≅ ℤ × ℤ_p^×` | 部分 | `PadicInt.unitCoeff_spec`、`valuation_mul/inv`（逐元素分解已在） | 只缺打包 `MulEquiv` |
| `ℤ_p^×` 分解 | 部分 | 剩余域半边完整（`PadicInt.residueField` 等） | Teichmüller/`rootsOfUnity` 在 `NumberTheory/Padics/**` 零命中；原料 `hensels_lemma`、`IsCyclic (ZMod p)ˣ` 在 |
| p-adic log/exp | **缺失** | 收敛工具齐（`dividedPowers`、`padicValNat_factorial_lt_of_ne_zero`、`CompleteSpace`） | log/exp 本体；且 `NonarchimedeanRing ℚ_[p]` 合成失败，卡住 `HasSum.mul_of_nonarchimedean` |
| Kummer（局部） | 部分 | 一般域论（`isCyclic_tfae` 等） | 关于 `ℚ_p^×/(ℚ_p^×)^n` 的一切 |
| 分歧/归一化 | **存在** | `ramificationIdx` 与 legacy 版及桥接；`valuation_liesOver` | 停在**分式域层**；完成域层重述缺失 |

- **最大缺口**：p-adic 对数（连同其使能的 `NonarchimedeanRing ℚ_[p]`）。其余是接口/包装。
- **最便宜的下一步（rank 0）**：`instance : NonarchimedeanRing ℚ_[p]`（数十行，`IsUltrametricDist`
  的加性半边已在触发）——它解锁 `HasSum.mul_of_nonarchimedean`，而后者同时挡在
  log 乘性证明与 Teichmüller 同态律的路上。

## 五、对象层：pilot 估值影子（`candidates/pilot-shadow`，提交 `d5818af`）

把 `(b₁,b₁,b₂,b₁)` 的**估值向量**做成真实对象（`Fin 4 → ℤ`，作用约定 `(σ•e) j = e (σ.symm j)`）：

| 定理 | 内容 |
|---|---|
| `orbit_mem_iff` | `v₁≠v₂` 时：`e` 在轨道中 ⟺ 每坐标是 `v₁` 或 `v₂` 且**恰有一个** `v₂` |
| `orbit_card` | 轨道恰 4 元 |
| `hull_eq` | 包络 = 常向量 `min v₁ v₂`（**不需要** `v₁≠v₂`，比要求更强） |
| `hull_strict_one_coordinate` | `v₁<v₂` 时，包络严格低于剖面的坐标集恰为 `{2}` |
| `swap23_moves_profile` | `v₁≠v₂` 时标号作用**改变**剖面 |
| `excess_is_uniform` | 每个槽位变体的包络都相同、且在 `swap 2↔3` 下不变，而剖面不是 |
| `relabel_toPadic` / `swap23_eq_labelAction` | `rfl`：整数作用就是 `IUTBridge.Slots.relabel`/`swap23` 的约定 |

**核验（我本人复跑，不采信报告）**：`lake env lean --json -DwarningAsError=true
Candidates/PilotShadow.lean` → exit 0、零诊断；`Candidates/Axioms.lean` → exit 0、
**10 条公理行全在 `{propext, Classical.choice, Quot.sound}` 内**、无 off-list；
`grep sorry|admit|opaque|^axiom|native_decide` → 0 命中；范围仅 `candidates/pilot-shadow/**`。

## 六、独立核验清单（哪些是我跑的，哪些是采信的）

| 断言 | 结论 |
|---|---|
| `PadicInt.unitCoeff_spec`、`PadicInt.residueField : ResidueField ℤ_[p] ≃+* ZMod p` | 已确认 |
| `Ideal.ramificationIdx` 与 legacy `'` 版桥接 | 已确认 |
| `valuation_liesOver` 位于 `IsDedekindDomain.HeightOneSpectrum`、停在分式域层 | 已确认（源码 + 探针） |
| **`NonarchimedeanRing ℚ_[p]` 合成失败** | 已确认（直接跑 `#synth`，失败） |
| `NormedAlgebra ℚ ℚ_[p]` 合成失败 | **未独立确认**（缺 import），仅记作基础设施路结论 |
| pilot 候选全部定理与公理 | 已确认 |

**方法论教训（第二次出现）**：缺 import 的探针报 "unknown constant" **推不出**不存在。
本轮我自己就把 `PadicInt.residueField` 误判为缺失一次；第六轮也曾用失败的名字探针
去论证"无法形式化"。缺席断言必须 **import 完整 + 源码 grep** 双证，且仍只意味着"当前没找到"。

## 七、交付物

| 文件 | 内容 |
|---|---|
| `bridges/correspondence.json` | 机器台账：8 条对应（含分级）+ 3 候选 + 3 反等同 + 5 项可行性 + 6 项独立核验 |
| `bridges/correspondence_gen.py` | 生成器/校验器：拒绝引用未导出的 theorem id（首跑抓出我自己三处错误） |
| `research/exploration/correspondence.md` | 整合结论（人读） |
| `research/exploration/definitions-inventory.md` | 源语义清单（10 对象 × 5 字段，逐条引笔记行号） |
| `research/exploration/log-kummer-feasibility.md` | 库级可行性（含 4 份探针与 digest） |
| `candidates/pilot-shadow/**` | 对象层 Lean 候选（`d5818af`，候选、未准入） |

提交链（`explore/correspondence`）：`d0dca3f` 台账本体 → `c3c6427` 合并语义清单 →
`c525805` 分级与反等同 → `652f1dc` 合并可行性 → `416a436` 可行性并入 →
`c30e4c2` 合并 pilot → `9d8a99b` pilot 并入。

## 八、未关闭与建议下一步

**未关闭**：G01–G06、RI-01–08 全部 open；Corollary 3.12 与 abc 未证；未构造任何 IUT 对象；
本轮所有结论都是候选或影子，**不进入 fact-tree**，不构成数学准入。

**建议顺序**（成本/阻塞排序，已写入台账 `next_targets`）：

0. `instance : NonarchimedeanRing ℚ_[p]` —— 最便宜，解锁 log 乘性与 Teichmüller 同态律；
1. Ind1–Ind3 作为**关系值**允许操作 + 投影方程（无库级阻塞；玩具投影公式已是
   `Slots.relabel_slotwise`）。约束：Ind3 是关系、`Allowed12` 严格小于全部 `A(k)`、
   `CompositionClosed` 是要证的目标而非假设；
2. 为 possible images 实例化 `SeededFamily`（容器形状已对，只缺一个实际 `c`；不得把族扩到
   恰好包含 witness）；
3. log-shell 的未阻塞半边（把 log 作为显式参数；但 `e_v=105,35` 时 `1/e_v≠1`，层索引不能整搬）。

## 九、复现

```powershell
python -B bridges/correspondence_gen.py          # 重新生成台账并校验全部锚点
cd candidates/pilot-shadow
lake env lean --json -DwarningAsError=true Candidates/PilotShadow.lean
lake env lean --json Candidates/Axioms.lean
```
