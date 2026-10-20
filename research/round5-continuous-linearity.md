# 第五轮：连续加法映射的 Q_p 线性及实际过滤后果

日期：2026-10-20（Asia/Shanghai）。本报告只覆盖 RI-01 中的一个结构子接口：**一旦已有真实 Q_p 拓扑模上的连续加法映射，就证明其 Q_p 线性**。真实 Ism、ind-topological G-module、H-invariants、log coordinates、log-image 与 seed 尚未构造。六项数学 gap 与八项真实实现义务继续全部 open；不宣称 Corollary 3.12、IUT 或 abc 已证明。

## 固定本地 Mathlib 的检索结果

以项目固定依赖 commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` 的本地源码为依据，不以滚动在线文档替代：

| 已有 API | 本地模块与行号 | 本轮用途 |
|---|---|---|
| `map_ratCast_smul` | `Mathlib/Algebra/Module/Rat.lean:29` | 加法同态自动与有理数经域强制转换后的标量作用相容；无需额外输入 Q 线性 |
| `Padic.denseRange_ratCast` | `Mathlib/NumberTheory/Padics/PadicNumbers.lean:815` | Mathlib 实际 Q_p 中有理数像稠密 |
| `DenseRange.equalizer` | `Mathlib/Topology/DenseEmbedding.lean:381` | 到 Hausdorff 目标的两个连续函数若在稠密像上一致，则处处一致 |
| `map_real_smul`、`AddMonoidHom.toRealLinearMap`、`AddEquiv.toRealLinearEquiv` | `Mathlib/Topology/Instances/RealVectorSpace.lean:25,37,51` | 已有实数版本，作为实现模式参考；不能直接应用到 Q_p |

定向检索覆盖 `Topology/Algebra`、`NumberTheory/Padics`，并在 Mathlib 全库检索 `map_ratCast_smul`、`toRatLinearMap`、`map_smul_of.*dense`、`map_padic_smul`、`toPadicLinear` 等相关标识。未找到可直接调用的 p-adic 对应版本。这是明确范围内的检索结果，不声称不存在任何等价表述的已有定理。

## 证明设计与假设

固定素数 p。源和目标是实际标量域 `ℚ_[p]` 上的加法交换群与模，各有拓扑及 `ContinuousSMul ℚ_[p]`；目标额外为 `T2Space`。对于连续加法同态 f 和固定向量 x，比较两个关于 a 的连续函数：`f (a • x)` 与 `a • f x`。已有有理标量相容性使二者在 Q 的像上一致，稠密性使其在全部 Q_p 上一致。

证明不要求空间有限维或完备，也不要求事先给出 Q_p 线性。Hausdorff 条件是稠密延拓唯一性的显式条件。构造连续线性映射保留原始函数。对于加法等价，正向连续已足以构造代数 Q_p 线性等价；后续代数过滤推论无需另设逆映射连续。

实际后果复用既有 `Shell.lean` 与 `Filtration.lean`：一般集合若被连续加法等价保持，则其任意标量缩放也被保持；在基域 Q_p，保持真实 Z_p 最大理想像推出保持全部自然数理想幂像、非零元素的实际有限值 valuation，以及包含零的范数。集合像相等仍是显式假设，不能替换为单向包含。精确 valuation 结论只在基域 Q_p 实例化，不能直接搬到分歧扩张。

## 已实现声明

模块 `LocalFieldAudit.ContinuousLinearity`，源码 `local-field/LocalFieldAudit/ContinuousLinearity.lean`。五条定理与两个构造如下；构造没有被拆成仅计数用的反身等式。

| 声明 | 源码行 | 类型与作用 |
|---|---:|---|
| `map_padic_smul` | 34 | 定理；从连续加法同态推出全部 Q_p 标量相容 |
| `toPadicContinuousLinearMap` | 45 | 定义；把上述证明打包为真正 `E →L[ℚ_[p]] F` |
| `toPadicLinearEquiv` | 52 | 定义；从加法等价和正向连续构造真正 `E ≃ₗ[ℚ_[p]] F` |
| `image_scalar_layer` | 57 | 定理；连续加法自同构保给定集合则保每个标量层 |
| `preserves_integerIdealImages` | 64 | 定理；保实际最大理想像则保全部自然数次幂的实际像 |
| `preserves_maximalIdealImage_valuation` | 74 | 定理；相同条件下保持非零 Q_p 元素的实际 valuation |
| `preserves_maximalIdealImage_norm` | 83 | 定理；相同条件下保持全部 Q_p 元素的范数，包含零 |

主引用路径为 `import LocalFieldAudit.ContinuousLinearity`；直接 imports 是 `LocalFieldAudit.Filtration`、`Mathlib.Algebra.Module.Rat` 和 `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`。本子任务没有修改主 import、catalog、EditorCheck、验证工具、fact-tree 或编辑器凭据。

## 验证状态

第四轮基线深查与归档完成、父代理放行后创建源码。首次严格 CLI 验证即成功，命令在 `local-field` 目录执行：

```text
lake env lean --json -DwarningAsError=true LocalFieldAudit/ContinuousLinearity.lean
```

退出码 0，stdout 为空，stderr 为空；无 Lean 诊断与告警。记录于 `local-field/verification/round5-astra-linearity-attempt-01.json`，时间为 `2026-10-20T10:28:52.8442484+08:00`；对应源码 SHA-256 为 `D88BB28CB8D9B6114B0F71FF51EC74E478485543E39C3FE60D19C640A05D114E`。文本扫描未发现 `sorry`、`admit` 或 `axiom`。传递公理白名单、目录依赖与实际 VS Code 准入由父代理继续执行；CLI 成功不等同编辑器准入。本子任务至此冻结候选 Lean 文件供父代理整合。

父代理最终验收补记：上述为 Astra 冻结候选时的历史状态。随后 Luna 完成构建与入口初检，父代理恢复面板并取得三份证明的匹配 `No goals`、入口 48 information／0 error／0 warning，绑定当前输入及运行产物哈希后，Luna 执行完整验证器成功：局部域 24 个准入节点、31 条边、0 pending。五条新 theorem 的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`；后四条均经辅助定义保留对 `map_padic_smul` 的目录依赖。最终范围与汇总见 [第五轮结果](round5-results.md)。RI-01 及全部真实 IUT 义务仍 open。
