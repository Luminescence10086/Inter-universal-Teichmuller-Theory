# 下一处需要证明的源比较

本轮终端工具已经以真实 Laurent 幂级数单位、约化限制类和实际赋值整数环工作。下一轮不再重复一般包络/审核工具开发，优先构造同一原始 IUT 实现中的下列输入。

1. 从原始允许输出的两种表示取得实际 germ 单位 r,s，而非任意 `ofData` 实例；标明所属 Hodge theater、分解群及同一系数 cyclotome。
2. 证明两者常数项的真实归一化等式 `constantCoeff r=a^m`、`constantCoeff s=b^m`。不能把 LGP 根 b 与 b^ell 混为同一个值。
3. 在第 mn 层构造并证明 `CoreDecompositionBridge.reducedClass ... r = reducedClass ... s`，逐个描述群、系数和标量作用的运输。两端必须真的属于同一个 H1 类型，不能通过重新定义另一端制造相等。
4. 给出独立的整数赋值差界 `< n`。若只有 ell-adic 塔上的比较，先证明精度随所需界可增长；固定第 ell 层不够。完整塔路线已在一般整数值赋值域验证。
5. 送入本轮终端定理后，将局部主格送入前轮 IntegralProductBridge/IntegralActionFrame；再单独证明跨标签/tensor/允许包络及度量相容。

比较的来源仍是核心 OPEN gap。当前只实现了 Laurent germ 模型；原始 tempered Pi 不在所审上游 IUT 项目的实现范围内，因此不能声称该模型已重建原始来源。Corollary 3.12 的全局包络/误差预算、abc 均未解决。

可独立交给机械 agent 的任务：固定源码定位与摘录、源/目标类型表、归一化层数核对、只读 manifest/哈希检查。下一步真正的数学工作是构造第1–3项，不能用把所需等式写成结构字段来替代。
