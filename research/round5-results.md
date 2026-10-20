# 第五轮：从连续加法作用到实际 Q_p 线性

日期：2026-10-20（Asia/Shanghai）。本轮按用户指定，将重复性工作交给 `gpt-6-luna`，将证明探索与联合实现探索交给两位 `gpt-6-astra`。准确分工及交接顺序见 [分工记录](round5-delegation.md)。**六项数学 gap、八项真实实现义务仍全部 open；IUT、Corollary 3.12 与 abc 均未证明。**

验收状态：**五条新定理已正式准入。** 最终 CLI、传递公理、辅助定义依赖追踪与实际 VS Code 门禁均通过；两工具链总图深查通过，合计 **62 个节点、45 条边、0 pending**。

新颖性说明：“新”指本工程新增的已验证声明，不代表学界首次发现。后续核查已找到连续加法映射 Q_p 线性机制的有限维文献先例；尚未建立任何成果的学术优先权。来源与初步完善路径见 [新颖性核查](round5-novelty-and-next-path.md)。

## 本轮补上的结构接口

RI-01 原先要求另外证明：实际 Ism 限制在有限坐标中给出的连续加法作用是 Q_p 线性的。本轮先解决一个独立且准确的子问题：给定实际 `ℚ_[p]` 上的加法交换群和模、各自拓扑、连续标量乘法以及 Hausdorff 目标，连续加法同态与所有 Q_p 标量相容。

证明先由加法性取得有理标量相容，再用 Mathlib 实际 Q_p 中有理数像的稠密性，将两个连续函数在稠密集上的相等延拓到处处相等。没有把待证线性放进接口字段；也没有假设有限维或完备性。加法等价只需正向连续，即可构造代数线性等价；源码没有声称逆映射连续。

这减少了将来真实 RI-01 实现需要独立提供的条件，但仍须构造真实 G-module、单位映像、H-invariants、有限坐标和连续作用，并证明其保持所需实际格。不能把本轮的泛型作用直接称作 Ism 元素。

## 五条定理与两个辅助构造

源码为 `local-field/LocalFieldAudit/ContinuousLinearity.lean`。以下五条 theorem 才是本轮目录目标；两个构造只作为辅助定义参与真实依赖追踪。

| theorem（命名空间 `LocalFieldAudit.ContinuousLinearity`） | 精确范围 |
|---|---|
| `map_padic_smul` | 连续加法同态满足所有 Q_p 标量相容 |
| `image_scalar_layer` | 连续加法自同构若保持指定集合的像相等，则保持其全部标量层，包括零标量 |
| `preserves_integerIdealImages` | 基域 Q_p 上保持实际最大理想像的连续加法等价，保持其全部自然数理想幂像 |
| `preserves_maximalIdealImage_valuation` | 同一基域条件下，保持非零元素的实际 valuation |
| `preserves_maximalIdealImage_norm` | 同一条件下保持所有元素的范数，包括零 |

`toPadicContinuousLinearMap` 将已证线性与给定连续性打包为 `E →L[ℚ_[p]] F`；`toPadicLinearEquiv` 将连续加法等价打包为 `E ≃ₗ[ℚ_[p]] F`。后四条定理通过后一个构造依赖 `map_padic_smul`，因此最终图必须保留穿过辅助定义的目录依赖。

集合像相等是后三条过滤结论的显式条件，不能弱化为单向包含。涉及有限值 `Padic.valuation` 的结论保留非零条件；范数结论单独覆盖零。基域的精确 valuation 保持不能直接替代分歧扩张中所需的粗层、log-image 与归一化证明。完整类型与源码行号见 [连续线性报告](round5-continuous-linearity.md)。

## 联合见证的未形式化探索

另一位 Astra 对固定缓存中的 IUT II/III 进行了定向来源审计，交付 [联合实现候选报告](round5-joint-realization.md)。它不包含 Lean 证明，不能作为本项目已认证数学结论。

报告建议进一步核查三个具体问题：固定 radial object 的 fullness 是否覆盖所需 κ、seed-region 与 action 联合数据；动作后改变代表的两阶段 `(κ,a)` 表示如何进入原 possible-images family；每个 place 的同步条件如何与 label 无关。后续不应未经证明就把复合映射重新命名为 relevant Kummer isomorphism，也不额外强加 κ 代表始终不变的要求。

torsion-orbit／fractional-ideal 路线与 kernel-orbit 检验仅是下一轮可失败的研究候选。真实 seed、联合 lift、region membership 和原容器身份均未实现；RI-03–05 和 G03 的状态不变。

## 固定环境与证据

继续使用固定 Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` 与 Lean `4.34.0-rc2`，只读复用已安装依赖。四份本轮相关 Mathlib 源码已按固定 commit 缓存并逐项核对 SHA-256，见 `round5-source-cache/manifest.json` 与根目录 `verification/round5-source-hashes.json`。已有实数版本只作为实现模式参考，不被当作 Q_p 定理使用。

第五轮开始时，Luna 已重新深查两工程第四轮基线：57 个节点、35 条边，绑定的旧观察及源码/运行产物快照一致，见 `round5-baseline-audit.md`。两工程的第四轮工具、图及证据分别归档于各自 `verification/round4/`。主工程 Lean 源码与工具没有变更，后续保留其第三轮实际 VS Code 观察并重新深查当前哈希。

新源码首次严格 CLI 检查退出 0、stdout/stderr 均为空，日志为 `local-field/verification/round5-astra-linearity-attempt-01.json`。冻结源码 SHA-256 为 `d88bb28cb8d9b6114b0f71ff51ec74e478485543e39c3fe60d19c640a05d114e`。实际编辑器观察完成后，父代理才绑定新 receipt，再执行最终验证器；任何阶段不足均不得准入。

本轮实际编辑器记录包含三份证明的匹配 InfoView：`Filtration.lean:215:29`、`Shell.lean:95:23`、`ContinuousLinearity.lean:86:86` 均显示 `No goals` 和 `Goals accomplished!`；入口展开 All Messages 后显示 48 条信息，状态栏 0 error、0 warning。父代理在绑定 receipt 前重算 15 个输入与 13008 个运行产物哈希，与预检 context 一致。

原始过滤 UI 文本、实际截图观察与时刻说明位于 `local-field/verification/vscode-observation-round5.txt`，最终 SHA-256 为 `58a6e74ff9f61ea4e26e01ab87b90a15fc36c6bf0f4acd475be0e4149060156a`。截图标识可能重复，记录时间是 capture 返回后代理时钟的时刻；不冒称保存了防伪图片证书。Paperproof 面板与异步旧位置问题的已解决工程记录见 [GAP-round5-editor.md](../GAP-round5-editor.md)。

## 最终准入与依赖图

Luna 在父代理明确绑定 receipt 后才执行完整验证器，结果为 `Admitted=24, pending=0, edges=31`。四份源码检查（主 import 加三份证明文件）退出码均为 0，stdout/stderr 均为空。入口 CLI 产生恰好 48 条 information，没有 warning/error；全部项目 theorem 的传递公理均在 `propext`、`Classical.choice`、`Quot.sound` 白名单内。

| 工程 | 准入节点 | 边 | 待验收 | 本轮依据 |
|---|---:|---:|---:|---|
| 主工程 Lean 4.34.0 | 38 | 14 | 0 | 沿用第三轮实际 VS Code 观察；第五轮深查输入及运行产物一致 |
| 局部域 Lean 4.34.0-rc2 | 24 | 31 | 0 | 第五轮完整 CLI、公理与实际 VS Code 验收 |
| 两独立图合计 | 62 | 45 | 0 | 总入口 `refresh --deep` 通过，无跨工具链证明边 |

新五条 theorem 增加十条目录依赖边。父代理逐项复核实际导出的 statement 与依赖：后四条均含 `map_padic_smul` 的依赖边，另外分别连接 Shell 的标量层或 Filtration 的实际过滤定理。两个辅助构造没有被计作节点，经过它们的证明依赖没有丢失。

主工程事实图哈希保持 `a94243eaeafbaf8161a2f2737965c01c5d05da6455a25cc1dbaa1e4aac7730e9`；本轮局部域事实图哈希为 `84af39856c7ff2e88ec4100c6e00636dfb824a142f2cd081b2ada5c95928843b`。最终命令与汇总审计保存在根目录 `verification/round5-final-audit.json` 及局部域 `verification/round5-final-verifier.json` 等日志中。

## 调用与剩余工作

已完成两个查询 smoke，可从根目录调用：

```powershell
python tools/forest.py query map_padic_smul
python tools/forest.py query ContinuousLinearity
python tools/forest.py refresh --deep
```

正式权威入口分别为两工程 `fact-tree/facts.json`；`fact-tree/catalogue.md` 只聚合独立工具链的图，不制造跨版本证明边。源码级复用导入 `LocalFieldAudit.ContinuousLinearity`。

下一条真实实现目标仍是 RI-01 的带类型坐标方块，以及 RI-03→RI-04→RI-05 同一 seed、κ、σ 的联合见证。不能用增加条件式定理数量代替这些对象的构造。全部开放义务及关闭标准见 [GAP.md](../GAP.md) 与 [真实接口台账](round3-realization-obligations.md)。
