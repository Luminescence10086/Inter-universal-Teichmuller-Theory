# 核心 Kummer 比较：2026-10-24

本轮把真实连续 Kummer 核定理接到了真实 Qp 离散赋值与主 Zp 格，另证明连续 H1 映射的一条充分反映判据。数学内容为标准 Kummer/离散赋值方法的组合；不声称是文献中从未出现的新定理，也没有解决 IUT 核心争议。

## 已编译的工具

隔离工程：`candidates/core-kummer`，Lean 4.34.0-rc2，Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`。`lake build CoreKummer` 使用 `warningAsError=true`；最终成功日志为本目录 `core-kummer-build.log`。23 个本轮选定声明及 2 个上游关键声明共 25 条公理报告，仅使用 propext/Classical.choice/Quot.sound。实际编辑器观察另存 `editor/`；没有观察完成的声明不进入正式 fact-tree。

收尾状态：三个核心文件均已在实际 VS Code Lean 扩展中处理至末尾，分别得到 13/10/2 条信息，零错误、零警告（桥接文件的 10 条包含 2 个上游声明）。记录与源文件 SHA256 保存在 `editor/observations.json`；已生成独立 `VERIFIED_LOCAL_SHARD` 分片，23 节点、37 边；未修改中央 registry。M1/M2 的交付候选不在此分片内，仍待其自身编辑器验收。

- `CoreKummerValuationSeparation`：13 个声明。真实幂差见证 x/y=z^n 给出 n 整除 v(x)-v(y)。独立严格界 |v(x)-v(y)|<n，或无界精度层，分别推出赋值与主格相等。源文件位于 `candidates/core-local-global/KummerValuationSeparation.lean`，通过新工程的 ValuationSupport 库构建；未改旧工程配置。
- `CoreKummerClassValuationBridge`：8 个声明，使用实际 `KummerTheory.kummer` 与已证明的 `ker_kummer`，不是把结论作为结构字段。相等类给出幂差见证；有限界或完整塔继而确定主格。`level_power_is_trivial` 显示 n 次幂在第 n 层消失。互素 m,n 可以在该有限层消去 m 次幂。
- `principal_eq_of_normalized_kummer_tower`：m 非零时，所有 ell^k 层上的 κ(x^m)=κ(y^m) 已足以推出 x Zp=y Zp；允许 m=ell，不要求互素。这是归一化同素数塔路线的精确接口。它恢复主格，不恢复所选根或某个有限层的根类。
- `CoreCohomologyReflection`：2 个声明。对实际 `ContH1.map`，若群映射连续满射、系数映射为连续乘法等价且作用兼容，则 H1 映射单射。没有断言 IUT 原始比较满足这些假设。

## 上游来源和移植边界

IUT 固定源码：`reviews/core-round/external/iut`，commit `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`。其 manifest 指定 continuous-kummer-theory 的 `98b67dfe9c82415aa17caa633d93960b6829af2e`；本轮用 Git 取得该精确版本，保存在本目录 `continuous-kummer-pin`。旧 external clone 的 `1d5194fc...` 不匹配该 pin，不能混用。

从精确 pin 移入新隔离工程的四个 Apache 2.0 文件：ContH1/Basic、Hilbert90、Kummer/Basic、Kummer/Equiv，保留版权和 LICENSE.upstream。原版 Lean 4.32 源码移至当前环境，只将四处 Prop 型局部 `haveI` 改为 `have` 来满足新版 linter，未关闭 linter。补丁见 `upstream-port.patch`。固定版没有新版 clone 的 ContH1/Inflation.lean，不能依赖那个后来的文件。

`upstream-port-build.log` 是移植修复前的失败尝试，保留作过程记录；不用于通过判断。通过证据仅为最终 `core-kummer-build.log` 及独立导出和编辑器记录。

## 为什么要分清“根”与“幂类”

以下是对固定上游源码的审读和下一步设计，尚未在本工程编译整个 IUT/Tate 项目，不能升级为已完成的原始 IUT 实例。

`Iut/EtaleTheta/KummerClass.lean` 明示不含原始 tempered Pi；其 `decomposition_kummer_etaleThetaGerm` 在 Laurent/germ 模型中把限制及系数约化后的类识别为残值 Kummer 类的 inflation。`thetaUnit_neg_sq` 给出 theta(-U²)=U^-1·etaleTheta(U)。

在相应标签求值和归一化后，`EtaleTheta/Wall.lean:qroot_pow_ell_mul_thetaRatio` 对应 a_j=b_j^ell，b_j=lgpValue(D,v,j)，并非 a_j=b_j。因此不能拿第 ell 层 κ(a_j) 当作 κ(b_j)。在真实 Kummer 模型上，本轮已 Lean 检验 κ_ell(b^ell)=1。

前轮根的单位根不定性（比值有限阶）和本轮有限 Kummer 类相等（比值是 n 次幂）也是两件事：后者不能直接套单位/根的主格稳定性。新工具显式要求赋值界或无界塔，避免该跳步。

## 未解决义务与最短路径

1. 在同一个原始 Hodge 实现中构造 tempered 来源、分解群与同步 cyclotome 的实际比较方块。不能用任意 `ofData` 或把目标等式当字段替代。
2. 将 germ 定理中的 restriction/reduceMu/inflation 对应到该来源；证明所需映射反映类相等，或直接证明本路线所需的赋值信息可反映。新 H1 单射判据提供充分条件，但 decompositionMap 满射和系数等价仍须具体证明。
3. 处理归一化 a=b^ell：优先证明同步的完整 ell^k 类比较并接新 normalized tower 工具；若只能取得有限层，必须另给独立赋值界与正确的消幂/升层步骤。
4. 从 Qp 推广到原始坏点有限扩张 completionAt：用规范化整数值赋值与实际整数环重建同样的核到主格桥接，处理 ramification 和归一化。当前结论明确只在 Qp，不把 Qp 当作任意 K_v。
5. 将得到的局部主格等式送入前轮 IntegralProductBridge/IntegralActionFrame，检查 tensor、允许包络和度量的兼容；全局误差/Corollary 3.12 仍另外开放。

原有 G01–G06、R-01–08 及 native-source extraction gap 均不据此关闭。交付审查另见 `delivery-review.md`，与数学准入分开记录。

## 调用与快速复验

`python -B research/core-kummer-2026-10-24/index.py --query normalized_kummer_tower` 按声明名或片段读取精确 Lean 类型、公理和依赖边；`--check` 检查已保存验证输入的字节新鲜度，不重新编译。重新生成索引使用不带参数的命令；生成器只读取 Lean 导出与观察证据，不调用 Lean 或操作编辑器。

依赖方向始终为 A→B 表示 B 的类型或证明直接使用 A。23 个本地声明之外的 Kummer/Mathlib 常量列作外部依赖边界；2 个上游核/等价声明在桥接文件中实际运行 `#print axioms`，不冒充本轮原创。全部三个文件编辑器验收记录齐全时，生成器写独立分片 `fact-tree/core-kummer-2026-10-24.json`；中央 registry 保留原状态。

并行情况：Astra/Luna 子任务提供了局部源码线索及 ValuationSeparation 初稿，但本轮触及用量上限，未完成其承诺的报告/验收；移植、修复、构建和验收由主 agent 接手，不把未完成子任务记成 PASS。
