# GAP：固定 native q 与同一合法输出的结构实现

状态：OPEN，2026-10-23。属于 `GAP-core-comparison-reconstruction.md` 的具体子义务。

本轮原文核查定位到 III Remark 3.9.5(ix) 的 cQ3/cQ4、Remark 3.11.1 的实际算法箭头复合，以及 Remark 3.12.2(v) 印刷194–195页的固定1-column精确读数解释。尚未将该复合实际构造成带结构 poly-morphism、作用、localization、log-Kummer 路径和归一化的 Lean 联合对象，也未证明它属于原始允许输出族。

已经形式化的外逼近量词准则和紧致联合近可行性准则，只证明一般充分条件。它们未构造 IUT 输入、允许选择或上述联合对象。外部 `Ind3` 未提供本路线需要的拓扑、紧致性及输出 USC；这些不是可直接采用的原文已证前提。

当前停留在原始来源类型与实现义务，避免反复尝试仅在数值层改写目标。下一步应先确定实际对象/箭头及其共同端点；若按有限精度重构，则另证同源数据联合可满足。未完成前不关闭 Cor3.12、abc 或既有 GAP，不准入新节点。

2026-10-23 结构推进：`candidates/core-local-global/NativeFiber.lean` 已构造参数化的固定-native 表示范畴，保留 localization 同构与结构箭头轨道，并证明规范化、框架变换判别及“局部表示不自动下降”的范畴反例；最终14条选定导出声明通过 CLI 公理检查。它尚未实例化原始 IUT 的 native 对象、线性/等变局部范畴、localization functors 或 formal quotient。普通全局箭头下降只是候选路线之一，未认定为原文必须满足的条件；形式商中的比较路线仍保留。详见 `research/native-fiber-2026-10-23.md`。本 GAP 保持 OPEN。

2026-10-23 M1–M4 回传后推进：静态索引经44项哈希／版本核对接收，解释性限制见 `research/core-backward-acceptance-2026-10-23/README.md`。新增 `RelativeDeterminant.lean` 和 `IPLCoherence.lean`：带参考层的相对行列式、带权幂归一化、实际 ℚ₃ 截面／系数球符号校准、IPL 箭头词的交换方块约化与代表差异自同构；19条选定导出声明通过 CLI 标准公理检查。这些仍为模型内结果。未把范畴差异实现为原始 IUT 上的矩阵／degree 字符，未证明允许 twists 在该字符下为零，未构造最后评价到原始允许 hull 输出的映射；没有 VS Code 新文件观察或 fact-tree 准入。详见 `research/core-normalization-attack-2026-10-23.md`。本 GAP 保持 OPEN。

2026-10-23 整数格实例推进：新增 `Collections.lean`，将局部 realification 与全局 localization 分离，构造遗忘函子、指定箭头／同构的提升判别、结构搬运，并给出非满的通用范畴回归。新增 `IntegralScalarOrbit.lean`，在非零整数标量乘法的具体局部模型中推出自同构范数为1，构造轨道上的实对数范数读数；实际 ℚ₃ 的 uniformizer 3 不落入 identity 轨道。新增 `IntegralMatrixCharacter.lean`，构造 GL_n(ℤ_p) 到该秩一范畴的行列式函子，从整数逆实际推出零行列式字符。三份文件24条选定导出通过严格 CLI 构建及标准公理审计。尚未把原始允许变化识别为保持同一 reference lattice 的整数格自同构，未构造其 Galois/单位相容作用、外层形式商或最后评价到原始允许 hull 输出的映射；原始 local-global 实例与整体 degree 比较也仍未完成。详见 `research/core-integral-realization-2026-10-23.md`。新文件无 VS Code 观察、未准入 fact-tree，本 GAP 保持 OPEN。

2026-10-23 同格保持推进：`LatticeStabilizer.lean` 已从 GL_n(ℚ_p) 对同一个 `B(ℤ_p^n)` 的像相等构造整数矩阵与整数逆，证明任意坐标帧下的 determinant norm=1；单向保持只推出 determinant norm≤1。`SaturationGrowth.lean` 已在实际 𝔽₃² 中核验 determinant-one 剪切、3→5 的并集增长、坐标环理想 hull 达到9点及实对数计数增量 log3；它是有限模型，未提升到 p-adic Haar 测度，更不是原始 IUT hull 的反例。两文件23条选定声明通过严格 CLI。下一项来源义务是实际 log-shell 的满秩格坐标及原操作识别，并分别估计饱和／更大系数环 hull 的增长，不能由单个自同构零字符推总增长为零。原始 native q 的合法输出实现、global comparison 及外层 formal quotient 仍未完成；本 GAP 保持 OPEN。详见 `research/lattice-stabilizer-saturation-2026-10-23.md`。

2026-10-23 Haar／有限商推进：新增 `ResidueHaar.lean`、`PadicSaturation.lean`、`ResidueHull.lean`、`ResidueModule.lean`，40条选定声明通过严格 CLI，全库104项标准公理报告。有限计数现已接到真实归一化 Haar 体积，实际 ℤ₃² 回归为1/3→5/9→1；半线性有限模商可证明无限操作族的共同子模 hull 覆盖上界，实对数版本明确要求正体积。尚未把该子模 hull 或共同容器识别为原文每个分量非零的 `λ·O` 型 holomorphic hull，也没有原始允许操作／同源 native q／degree 的实例化。详见 `research/residue-hull-2026-10-23.md` 与 `GAP-core-residue-hull-realization.md`。新文件无 VS Code 实际观察、未准入 fact-tree；本 GAP 继续 OPEN。

2026-10-24 来源接线推进：新增 `IntegralProductBridge`、`IntegralActionDescent`、`IntegralActionFrame`、`TorsionHullStability`，49 项选定声明通过严格主线 Lean 构建及实际 VS Code 文件检查，均零错误零告警。整闭包现可沿实际 reduced-Artinian 分解构造成乘积；同格自同构在任意已给定 frame 的共同有限商上实际作用；有限阶根选择不改变相应域中主整闭包集合。它们没有供应原始 native 输出。

本轮来源核查把下一义务收窄为：同一坏处、同一 capsule 的原始同步 Θ-Kummer class 经 decomposition restriction 后，是否给出指定 `lgpValue D v (i+1)` 的 Kummer 像。外部已有显式 Tate theta 与 tensor-factor 接口，也有 Hodge 模型类型；尚缺的是原始 Hodge/IPL 来源到这些模型的实际提取与识别，不能泛称“没有类型或任何 out 实例”。product-formula 的全局主因子捷径因没有来源构造而暂停。细节见 `research/core-next-2026-10-23/native-next-interface.md` 和该目录 `GAP-native-source-extraction.md`。本 GAP 保持 OPEN，未据新工具关闭原始比较、Cor3.12 或 abc。
