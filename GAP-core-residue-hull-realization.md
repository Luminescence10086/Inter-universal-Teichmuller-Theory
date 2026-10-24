# GAP：有限商证书到原始 holomorphic hull 的实际实现

状态：OPEN，2026-10-23。

已严格 Lean 验证：真实 p 进标准格的有限剩余类计数／归一化 Haar 桥；系数环明确的半线性商、子模 hull 的精确圆柱公式；无限操作族的共同有限子模覆盖上界；正体积条件下的实对数上界。真实 ℤ₃² 例子已核验 1/3→5/9→1。

这些结果尚未实例化 IUT III Remark 3.9.5(i) 中的原始 hull。尚缺：

1. 原始系数环与同一有限正体积参考格上的真实作用、有限模商。
2. 所有原始允许变化对同一个商的交换关系，及同源的 native q／输出来源。
3. 有限共同子模 J 的覆盖证书，并证明拉回容器是每个直和域分量均非零的 `λ·O` 型原文允许 hull 容器，或另证该情形下子模 span 等于原文 hull。
4. 参考格归一化体积到原始 log-volume、packet 权重和最终 arithmetic degree 的转换。

未解决以上义务前，不声称已经得到原始 IUT hull 估计、Corollary 3.12 或 abc。没有把 shell 保持、ℚ_p-linearity、坐标环的理想 hull 或单个像保体积当作替代证据。

详见 `research/residue-hull-2026-10-23.md`。本 GAP 是具体实现义务记录，并非宣称原文存在已证明的缺陷；与 `GAP-core-native-realization.md` 同时保持开放。

2026-10-23 主格推进：`PrincipalProduct.lean`、`PadicPrincipalHull.lean` 在实际 `ℚ_p^n`／`ℤ_p^n` 中，从有限商核的非零分量成员构造 `λ·O` 型容器，证明紧性、候选体积为正、真实环境 Haar 计数公式、无限操作族共同容器及非空完整圆柱集的环境最小主格性质。两文件23项选定声明严格 CLI 通过，全库127项标准公理报告；无本轮 VS Code 观察、未入 fact-tree。此进展关闭的是分裂模型中的形状／环境测度子义务；原始有限扩张系数环、共同分式参考格、全体允许操作、native q 与 degree 归一化仍未实例化。详见 `research/principal-hull-2026-10-23.md`。本 GAP 保持 OPEN。

2026-10-24：通用 `IntegralProductBridge.artinianIntegralEquiv` 已把整闭包的 reduced-Artinian 乘积分解构造成真实代数同构，而非仅逐坐标 membership；`IntegralActionDescent` 与 `IntegralActionFrame` 已从同一加法格稳定性构造共同有限商及实际环境作用方块；`TorsionHullStability` 处理有限阶根选择对域中主整闭包集合的影响。四文件49项选定导出已严格构建并实际 VS Code 零错误零告警。来源核查同时确认 `tensorLogShell` 与 maximal order 不能一般认同；上述共同商首先针对被稳定的加法格，不自动给出最大整环 hull 的共同商或所有原始操作证书。原始 packet 特化、共同系数环作用、native q 来源和 degree 归一化仍未完成，本 GAP 保持 OPEN。验证入口见 `research/core-next-2026-10-23/README.md`。
