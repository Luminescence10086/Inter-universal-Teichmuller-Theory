# 第三轮：G03 最小真实接口研究台账

更新日期：2026-10-20（Asia/Shanghai）。本台账原始来源拆分使用 2026-10-16 已缓存、已登记版本的来源，没有重新联网检索。原始台账写作没有修改 Lean、验证器或 fact-tree，也没有运行新的 Lean 检查；后续工程与验收结果分别在各轮补记中记录。

第四轮补记：基域 ℚ_p 的实际最大理想过滤、严格估值层和线性保持子接口已新增至 `LocalFieldAudit/Filtration.lean`，具体验收以 [第四轮结果](round4-results.md) 为准。RI-06 的真实 logarithm-image 身份、RI-07 在指定分歧扩张与实际 Ism 上的实现，以及 RI-03–05 的联合见证均未因此完成；八条状态继续为 open。

第五轮补记：`LocalFieldAudit/ContinuousLinearity.lean` 实现连续加法作用到 ℚ_p 线性的结构子接口，准确假设与最终验收状态见 [第五轮结果](round5-results.md)。这处理 RI-01 所列线性证明子问题，但没有提供其真实有限拓扑模、坐标、连续作用或保格实例。另有 [联合实现候选](round5-joint-realization.md)，强调同一联合源数据出发的允许路径，允许动作后改变代表；两阶段输出与同步条件尚未形式化。八条真实接口仍全部 open。

**状态：八条真实接口全部保持 open。** 下列 theorem 名称是拟议目标，不表示已有源码或已通过验收。验收补记：LP0 的纯线性集合缩放部分已由 `LocalFieldAudit/Shell.lean` 五条明确前提下的定理实现，并通过 CLI 与 VS Code 验收，见 [第三轮结果](round3-results.md)。这没有实现本台账所需的真实 IUT log-shell、Ism 或 packet。所有数学解释、反例机制和修补方案都受用户的 Lean 验证标准约束。

依据：[第三轮语义审计](<D:/Inter-universal Teichmüller Theory/research/round3-semantic-audit.md>)、[第三轮来源登记](<D:/Inter-universal Teichmüller Theory/research/round3-sources.json>)；必要的旧文定位见[第二轮来源审计](<D:/Inter-universal Teichmüller Theory/research/round2-source-audit.md>)。

## 使用规则与共同前置

- 原文**已有** Ism 与 ×μ-Kummer orbit 的定义。待建的是这些对象的真实有限局部实现，不再使用“原文没有允许族或 orbit 定义”的说法。
- Ind3 按 upper-semi-compatible 的有向包含／满射处理，不要求 Ind1/2/3 合成一个可逆群作用。
- 优先建立固定 seed、固定实际 Kummer choice、σ=(2 3) 的一条**联合允许**见证路径。全体 possible images 的任意复合闭包不是第一阶段必需目标。
- 不把 κ 的边缘允许性和 σ 的边缘允许性拼成联合允许性；不把所有有限壳格自同构直接当成真实 Ism 元素。
- 源数据 D₂ 的真实 initial Θ-datum 实例、局部完成域、p 的素性和相关分歧数据是共同前置，不能从短文数表直接作为已证事实导入。若暂以参数研究，结果必须标为条件式。
- 每项下一步交付一个“对象定义＋准确声明＋依赖清单”；真实来源的实现证明与泛型条件式分别登记。验收沿用项目流程：检查声明、公理依赖、无占位证明，并在用户指定的 VSCode 环境运行至零告警；本台账不代替该验收。
- 下述“可失败判据”仅用于否定相应候选接口或指定路径。编译失败、定义未完成、检索不到现成定理都不等于数学反证；指定路径失败也不等于整个 IUT 被反驳。

## RI-01：finite_Ism_realization

**当前来源证据。** IUT II Example 1.8(iv), p.39 对每个 open H≤G 保持单位像 lattice；Definition 4.9(i), p.154 用这些 H-lattices 刻画 Ism-orbit。AbsTop III Prop.5.8(i)–(iii), pp.139–140；IUT III Prop.1.2(vi), p.32 提供重建与 log-shell 相容性依据。这些是来源定位，不是本工程证明。

**缺失对象。** 真实 ind-topological G-module U(G)、单位到 torsion quotient 的 map、取 H-invariants 的有限模块、log coordinates，以及真实 Ism 动作的限制。须区分“单位先取 H-invariants 后映入 quotient”与“quotient 的全部 H-invariants”。

**下一条 Lean 目标。** 拟议 `finite_Ism_restriction_preserves_log_lattice`：对实际 G、每个相关 open H、每个 s∈Ism(G)，构造其在有限 V_H 上的 continuous additive equivalence，并在具体 log coordinates 中证明它是 Q_p-linear 且把 L_H 映到自身。先取 H=G 建立第一个实例，再扩展 H；连续加法映射到 Q_p-linearity 的引理必须显式给出。

**下一动作／交付。** 画出单位、quotient、log、invariants 的带类型交换图；实现一个有限 H 的坐标方块。只需要证明真实限制落入 A(k)，不要求每个 A(k) 元素都扩张为 Ism。

**可失败判据。** 若实际限制不保持选定有限子空间，或坐标中的 L_H 不是所称的 log_p(O_k^×)，该接口须改写；不能靠把目标 lattice 定义成“任意被保持的格”绕过。有限 A(k) 的候选反例不能自动充当真实 Ism 反例。

状态：open；依赖共同前置。

## RI-02：Kummer_tensor_realization

**当前来源证据。** IUT III Prop.3.2(i),(ii), pp.97–99；Thm.3.11(ii)(a),(b), p.155 给 packet、splitting-monoid 的 Kummer 对应；IUT II Cor.4.6, pp.137–139 给同步的局部同构。其与 RI-01 的全部选择必须一致。

**缺失对象。** 实际 Kummer-choice 类型 c、holomorphic 与 mono-analytic 的有限空间及 lattices、局部 κ_c、direct-sum/tensor construction，以及选定坐标 ι_hol、ι_an。

**下一条 Lean 目标。** 拟议 `actual_kummer_packet_coordinate_formula`：对实际允许的 c，证明有限 packet map 等于逐 slot 的局部 direct sum maps 的 tensor product，并证明 χ_(c,i,v)=ι_an⁻¹∘κ_(c,i,v)∘ι_hol 保有限 log-lattice。为所选 tuple 给出 projection 方程。

**下一动作／交付。** 先在一个实际 c、一个 finite factor 上完成 κ 方块，再证明 tensor/direct-sum 分配同构中的方程。不得仅增加一个名为“κ 保 lattice”的结构字段就称实现完成。

**可失败判据。** 若实际 κ 不能在这些有限坐标下逐因子分解，或相关有限不变量／标量扩张不相容，需给出真实 map 并重算后续参数；抽象 packet 同构存在不满足本目标。

状态：open；依赖 RI-01 及实际 Kummer 数据。

## RI-03：specific_seed_realization

**当前来源证据。** IUT III Prop.3.1(ii), p.93 的 tensor with 1；Prop.3.4(ii), pp.102–103 的指定 slot／place action；Prop.3.7(v) 与 Def.3.8(i), p.112 的 pilot 构造。Urahigashi §4 Lemma 3 把它们连成具体 seed membership。

**缺失对象。** 真实 Θ-pilot 的 image-region、其积分结构、splitting generator θ 的域定义与 root-of-unity 选择，以及从抽象 pilot object 到具体 subset 的实现。

**下一条 Lean 目标。** 拟议 `actual_pilot_seed_exists`：存在一个实际 m、允许的 c 及 g∈SeedRegion(c)，在 u⃗=(b₁,b₁,b₂,b₁) 的坐标中满足 `pr_u(κ_c(g))=χ(x)`，其中 x=1⊗1⊗1⊗θ，θ 的来源是 b₁，stage 指数为 3²。θ 的估值和非零性分别从实际算术构造取得。

**下一动作／交付。** 先给 SeedRegion 的原文实现定义，随后证明 membership。不能反向定义 SeedRegion 为“包含所需 g 的某个集合”。

**可失败判据。** 若原 pilot-region 实际不含该元素、θ 不在所称有限域，或所选 ideal／slot 与原 pilot 定义不一致，指定 seed 路径失败。必须记录失败的具体 map 或 membership，不升级为 IUT 总体结论。

状态：open；依赖 RI-02 和实际 splitting-monoid／pilot 实现。

## RI-04：specific_Ind1_lift

**当前来源证据。** IUT I §0 p.34、Def.4.10 pp.119–120；IUT III Thm.3.11(i), p.154 将 procession automorphisms 纳入 Ind1。IUT II Example 1.7, pp.32–35 提供 coric groupoid 与 lifting 的框架。来源支持并不自动给定指定 κ 与 σ 的联合 lift。

**缺失对象。** RI-03 所选 c 对应的真实 procession、σ=(2 3) 的一个实际 representative、它在完整联合数据上的 lift，以及源／目标 packet 的不同类型。不能只搬点而不处理 κ、action、lattice 与同步数据。

**下一条 Lean 目标。** 拟议 `specific_swap_lift_exists`：对已选 seed witness，构造至少一个实际允许的 a，其 permutation 为 σ，且给出
`pr_v ∘ R_a = (⊗ᵢ ψᵢ) ∘ σ_* ∘ pr_u`，
其中 v⃗=u⃗∘σ⁻¹=(b₁,b₁,b₁,b₂)，并证明每个实际 ψᵢ 满足 RI-01 所需有限条件。

**下一动作／交付。** 先给带 source/target 的 lift 见证和一次 projection 方程。复用已有泛型重索引源码时，额外证明实际 packet 到该泛型接口的 realization；当前文件存在本身不认证此实现。

**可失败判据。** 若该 σ 虽为 procession 自同构，却不能与 RI-03 的 κ 联合提升，或必须改变 source-place／积分结构，该指定路径须修正。分别存在某个 κ 和某个 lift 不足以排除该失败。

状态：open；依赖 RI-02、RI-03。

## RI-05：specific_output_membership

**当前来源证据。** IUT III Cor.3.12, pp.173–174 定义 relevant Kummer isomorphisms 与 Ind1/2/3 下的 possible images 之并；Remark 3.9.5(Ob5), p.134 讨论 possible-region family 及其 hull。已有 Ism/Kummer orbit 定义，不再要求从零补造一个并不存在于来源中的 orbit 概念。

**缺失对象。** 从原文提取的 `Adm(c)`、实际 output subset `out(c)`，以及它们与原 `U_j` 的对应。需要把 κ、σ、seed 与其它兼容性保留在同一 joint relation 内。

**下一条 Lean 目标。** 拟议 `specific_transported_seed_mem_possible_images`：为 RI-04 的同一 witness 构造 c′ 与 `Adm(c′)`，证明 `R_a(κ_c(g))∈out(c′)⊆U_3`。只需该一次实际复合；先固定可用 m，Ind2 可先尝试实际恒等代表。若跨 m 必需，明确给出所用 Ind3 inclusion，而非假设其有逆。

**下一动作／交付。** 写出原允许族到工程 family 的精确 map；用同一联合见证进入 U_3。泛型 `SeededFamily` 或 `familyImage` 可作容器，但要另证其与真实 U_j 一致，不能任意增大集合来制造 witness。

**可失败判据。** 若该 joint witness 不满足原 Adm，或工程 family 只是原 U_j 的过度近似，不能推出实际 membership。边缘允许性和“对所有 A(k) 矩阵的数值界”均不能补上这一缺口。

状态：open；依赖 RI-03、RI-04；这是当前优先审计的语义桥梁。

## RI-06：small_ramification_log_lattice

**当前来源证据。** IUT IV Prop.1.2(i), p.10 在 p odd、e≤p−2 的分支给具体 log-lattice 控制；Urahigashi §2–3 提供本例 p=30965771、e=105 或 35 的主张。这里仍须建立真实局部域实例及条件。

**缺失对象。** 每个实际 k_v 的 integer ring、maximal ideal、p-adic logarithm、ord_p(p)=1 的归一化、value group=(1/e_v)Z，以及源数据给出的 e_v 证明。

**下一条 Lean 目标。** 拟议 `actual_small_ramification_log_image`：在每个相关实际 k_v 证明 `log_p(O_v^×)=m_v`；再对非零 z、每个 n∈Z，证明
`z∈p^n log_p(O_v^×) ↔ n<ord_p(z)`。
log-image 等式与离散估值判别分开声明。

**下一动作／交付。** 先处理一个完成域；来源支持只确定研究目标，不把 Proposition 1.2 或 e 数表当作自定义公理。已验收的 LP0 纯线性部分可复用；真实 log-image 与估值层对应仍需另证。

**可失败判据。** 若 e 条件未满足、log-image 不是所称 maximal ideal、归一化不同或 quotient-invariants 被误认，则本分支不可用；转用有 a,b 误差的 lattice sandwich 并重算，不能保留原 ceil 推理。

状态：open；依赖共同前置；不依赖全体 Ind3 的群作用。

## RI-07：coarse_valuation_bound

**当前来源证据。** Urahigashi §1(1.3)、§5 使用 ceil 界；第三轮报告 LP0–LP4 已区分 lattice filtration 和 field valuation。现有 `LocalNumerics.lean` 使用的 `PreservesLayers` 是给定前提的模型接口，本台账不声称它已由真实 Ism 导出。

**缺失对象。** RI-01 的实际有限 χ、ψ 与 RI-06 的同一 lattice／valuation 实现之间的连接，以及 θ、1 的非零性与实际估值。保精细 valuation 不是必要目标。

**下一条 Lean 目标。** 拟议 `actual_local_map_preserves_ceil_order`：对所需实际 map 和非零 z，从 lattice 层保持及 RI-06 推出 `ceil(ord_p(Tz))=ceil(ord_p(z))`。随后仅对指定 witness 推出 `ord_p(ψ₂(θ))≤2` 和其它因子 `ord_p(ψᵢ(1))≤0`。

**下一动作／交付。** 先在有限 local-field 层证明粗层定理，再建立到模型 `PreservesLayers` 的桥梁；不同整数缩放的 valuation 要显式换算。核实零元素用扩展 valuation 处理还是由线性双射排除。

**可失败判据。** 若实际 map 不保 RI-06 的格、valuation 离散层识别失败，或坐标选择换了 lattice，该粗界不能直接用。精细 ord 值改变本身不否定 ceil 界；A(k) 内的候选 map 也不自动是实际 Ism witness。

状态：open；依赖 RI-01、RI-02、RI-06，并在 RI-03／RI-04 的实际 maps 上实例化。

## RI-08：normalization_hull_compatibility

**当前来源证据。** IUT III Remark 3.9.5(i), p.127 的 holomorphic hull；IUT IV Props.1.1–1.4, pp.9–13 的 tensor normalization、different 与 log-volume；Step(iv),(v), pp.26–28 的 tuple 局部估计。Urahigashi §5 使用 projected hull 是相应 R̃-module 的解释。

**缺失对象。** 实际 finite tensor packet 的 simple-field decomposition、R̃=normalization(⊗O_i)、真实 hull 所用 O 的坐标实现、tuple projection、相容 log-volume 归一化，以及 relatively compact／whole-packet 两种分支。

**下一条 Lean 目标。** 拟议 `actual_projected_hull_contains_integral_span`：对 RI-05 已证属于真实 U_3 的 witness y，证明其投影的 R̃-linear span 包含于真实 projected hull；随后从 RI-07 的逐因子界证明所需 `p²R̃⊆pr_v(hull(U_3))` 与相应 log-volume 下界。每个 simple-field component 的嵌入估值与 pure-tensor 求和必须单列桥梁。

**下一动作／交付。** 先证明 hull 的实际积分结构正是这里的 R̃，而不只是某个抽象 O-module；再证明投影、积分 span、体积三者相容。与 Step(v) 的容器比较必须确认是同一个原 U_j、同一个 tuple 和同一个归一化。

**可失败判据。** 若真实 hull 的 ring／integral structure 不是该 R̃、投影不能按假定识别、region 仅在别的容器中实现，或体积归一化不一致，不能把模型 non-containment 转移到原 IUT。即便此项完成，也只涉及指定局部步骤，不自动裁决全局 Theorem 1.10 或 abc。

状态：open；定义层可与 RI-01 并行；见证实例依赖 RI-05、RI-07。

## 执行顺序与验收出口

| 工作流 | 先交付 | 成功后的直接用途 |
|---|---|---|
| 有限实现 | RI-01 → RI-02 | 实际 maps 到有限模型；不申请全部 A(k) 的反向扩张 |
| 见证路径（优先） | RI-03 → RI-04 → RI-05 | 一条 κ/σ 联合允许路径；不要求普遍群闭包 |
| 粗估值 | RI-06，并接 RI-01/RI-02 → RI-07 | 从真实 lattice 到所需 one-sided valuation 界 |
| 几何与测度 | RI-08 定义层，再接 RI-05/RI-07 | 从真实 witness 到原 tuple 的 projected hull 比较 |

每次会话只在有新源码、精确来源反例或已通过用户验收的证明时更新相关状态。若只得到更强的条件式模型，登记它增加的假设，保留原接口 open。若指定路径失败，记录失败的最小 joint condition，并研究修补容器或替代路径，不以失败自动声称反驳 IUT。

**本次交付是可执行研究台账。G03、八条真实接口与原 IUT→abc 的整体认证均未关闭；纯线性子接口的验收不关闭这些 gap。**

