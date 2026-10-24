# GAP：原始多径算法的 q-pilot 比较实现

状态：OPEN，2026-10-22。研究任务已收束到此处；不是“已证明原文不存在证明”的断言，也不是本轮工具运行故障。

原文锚点：IUT III Remark 3.9.5(ix) 的 cQ3/cQ4、与 iQ5 的差别；Remark 3.11.1 的 IPL/SHE/APT；Corollary 3.12 proof (xi-d)–(xi-f)，特别是应用 log-volume 前的结构保持与可能的近似。

当前缺口：尚未在本站 Lean 中构造原始允许输出类型、上述复合操作及其 correlated Ind1/2/3 选择，并证明在同一输入与归一化下实现所需 q-pilot 比较。外部 `Iut.Wall.EtaAlg` 是接口候选；其 `realisation` 与本站所需原始语义的对应仍须建立。简化模型的不可推出不填补或否定这个缺口。

补救顺序见 `research/github-iut-core-survey-2026-10-22.md`：A1 源码语义、A2 真实 Kummer/theta 箭头、A3 允许 witness、A4 全局体积上界；B 线研究原输出上的近似覆盖与 hull 差。

关闭要求：真实类型和完整 Lean 证明、不将目标/等价目标假设化、明确原文对应、实际 VS Code 零错误零告警。当前不关闭 Cor3.12、abc 或既有 RI/G 节点。

2026-10-23 推进：Q3 两份对数已接线；外逼近量词准则、紧致联合近可行性及两个防止错误泛化的例子已完成 CLI 候选验证，共8条导出。细节见 `research/core-compatibility-2026-10-23/README.md`。原始 native q 与合法输出的联合来源实现仍未建立，单列为 `GAP-core-native-realization.md`。原文固定1-column的精确读数解释保留为主线核查对象；不将其预先替换成仅有标量上界的模型。
