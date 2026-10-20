# 探索成果的筛选、整合与形式化

日期：2026-10-20。本轮在现有 bridge 工程中整合可用工具，保留此前的研究与审阅记录。形式化对象是实际基域 `Q_p`、抽象有限槽及显式定义的关系；真实 IUT 对象及 G01–G06、RI-01–08 继续开放。本文不提出学术首创性主张。

## 保留的思想与精确接口

1. **层梯与缩放账本**：`ScaleLedger` 的层随整数指标严格反单调，缩放指数相加、有限复合可合并。`cost_exact` 仅是集合像身份，没有定义体积、代价或最优性。
2. **联合可容许性**：用矩形性检验联合关系能否替换为独立边际。任意固定目标层均可矩形化；非空的矩形子关系恰实现一个层。非空性只用于存在性，不能从空关系推出层见证。
3. **作用相容性**：对逐槽标量作用，交换判据恰为标量族的置换不变性。另保留可逆、非对角且与交换置换相容的混槽映射，因此不能把逐槽判据扩大为排除所有混槽作用。
4. **加权估值账本**：保留整数权重与置换、缩放的精确公式；手选 `(1,1,2,1)` 只作测试权重。范数乘积恒等式只使用无权总账本，不是一般权重的体积公式。

本轮新增的九条组合接口在 `bridge/IUTBridge/Integration.lean`，完整前提和审查见 [RESULTS](integration-astra/RESULTS.md) 与 [SELECTION](integration-astra/SELECTION.md)。逐条前提由 elaborated binder 审计与目录核对。

## 组合判据及定义域

记 `L_w(x) = Σ_j w_j v(x_j)`，`T(x) = relabel σ (slotwise a x)`，假设每个标量 `a_j ≠ 0`。精确公式为

```text
所有坐标非零：
L_w(Tx) = L_(w∘σ)(x) + Σ_j w_(σj) v(a_j).

任意坐标：
L_w(Tx) = L_(w∘σ)(x) + Σ_j if x_j=0 then 0 else w_(σj) v(a_j).
```

因此得到两个不同的 iff：

| 要求保账的输入域 | 充要条件 |
|---|---|
| 每个坐标均非零的全部元组 | 权重置换不变，且 `Σ_j w_j v(a_j)=0` |
| 包括零坐标的全部元组 | 权重置换不变，且每槽 `w_j v(a_j)=0` |

必要方向使用常一元组、含 `p` 与 `1` 的 delta 探针；允许零时还使用单坐标探针。若未来实际 admissible region 不包含这些探针，不能直接搬用必要方向。标量交换条件和账本保持条件也不能互相替代。

## 工程工具的整合

- bridge 的标准 `tools/verify.py` 转入 schema-3 验证器。收据同时绑定完整输入集合、依赖源码与外部 checkout 身份、实际导入 `.olean` 及现存 sidecar、Lean/Lake 程序、实际编辑器观察和每个源文件。验证失败关闭旧准入。
- `tools/freshness.py` 检查完整输入与运行环境；合同审计拒绝 pending 节点。新增源文件或非 Lean 配置变化也会失效。
- `tools/DefinitionBodies.lean` 在三工程重新导出定义体；BR-03 同时检查类型与定义体的打印文本。文本相等不是跨工具链语义证明。
- `tools/semantic_lock.py` 记录保留限定名的陈述、种类、模块、公理集及项目定义体指纹；与旧 `statement_lock.py` 并存。它是保守变更账本，等价改写也可能触发复核，不是“锁定数学含义”。
- `tools/forest.py` 接入 bridge 查询，并从实际常量依赖提取同工具链的 `local-field → bridge` 边。`core → bridge` 合同不进入内核证明边。

负测位于 `integration-engineering/`。实际 Lean 夹具的三组同类型、不同定义体比较均拒绝。单元检查覆盖配置/目录/源码集合漂移、运行产物与新增 sidecar、旧收据版本、缺少编辑器入口观察、模块/公理集与定义体变化。首次整体验证暴露了把外部包配置固定猜作 `lakefile.toml` 的实现错误；已改为读取 manifest 的 `configFile`，并增加 `lakefile.lean` 回归检查。

## 对真实 IUT 的接入路径

以下为研究计划，尚未证明：先实现实际对象、联合 admissibility 及作用到有限 `Q_p` 模型的映射，再证明该映射保留所需结构、权重和输入域；若作用确为逐槽形式，调用精确判据核算预算。混槽作用另证其变换律。最后另建测度/Arakelov 量、真实区域与定量比较，不能把范数乘积或层移动身份当作体积估计。

当前声明没有构造 Ism/Kummer、seed-region、log-image、holomorphic hull 或全局误差预算。没有证明 Corollary 3.12 或 abc。

## 验收和复现

最终完整 CLI 准入成功：bridge **73 个节点、67 条内部依赖边、0 pending**。逐项公理均在标准三项白名单内；五份证明源文件及主 import 的独立源码检查均无诊断。入口 CLI 与实际 VS Code 均为 **146 条 information、0 error、0 warning**。收据 schema-3 有效，观察前后 36 个输入、17 个依赖身份键与 14,998 个运行产物保持一致。

统一 fact-tree 深查重建为 **135 个节点、115 条边、0 pending**：主工程 38/14、local-field 24/31、bridge 73/67，另有 3 条实际 `local-field → bridge` 导入边。两套工具链的标准公理与外部库仍是依赖环境，没有把整套 Mathlib 当作逐一编辑器验收的新节点。

本地 HEAD `4e3f01c307d67ae2c0b1b1ce9723afda39376f4d` 的原两工程 31 项被验收输入均与 Git blob 和工作区字节一致，原 14 处行尾漂移已消除；两树独立 `--deep` 也通过。本轮整合是工作区改动，未声称已经发布到 GitHub。最后一轮 CLI 记录在 `integration-engineering/cli-final.json`，基线复核在 `retained-baseline.json`。

工程记录补充：准备期间追加审计 helper/负测，曾使正在运行的验证因工具输入变化而拒绝；在固定输入并取得实际 UI 观察后重跑通过，没有手改旧凭据来掩盖漂移。一次共享产物检查把新绑定的 `.olean.hash` 构建元数据也要求存在于旧 local-field 收据，检查过严而失败；排除旧收据未覆盖的该类辅助文件后，13,006 个共享产物及两个实际导入的局部域 `.olean` 全部相同，见 `import-identity.json`。

统一目录和 JSON 正确区分三个工程、两个 Lean 工具链；`forest.py refresh` 的控制台末行沿用旧的 `toolchains` 标签，其数字 3 是工程数量。显示标签不参与定理或依赖边的准入。

新的变更账本基线已生成，覆盖三工程 **312 个常量**，含陈述、模块、公理及项目定义体指纹。首次建档为 312 additions、0 changed、0 removed；旧 `statement-lock.json` 保留作历史数据，没有静默覆盖。该账本仅提供保守变更检查，不认证数学语义等价。

实际观察、收据与最终准入数量以 `bridge/verification/vscode-observation-round8.txt`、`vscode-receipt.json` 和 `bridge/fact-tree/facts.json` 为准。逐文件检查匹配文件名和末项证明的 InfoView `No goals`；入口逐条 `#check` 与 `#print axioms`，预期 146 条 information、零 error/warning。CLI 输出单独保存，不能代替编辑器观察。

```powershell
python -X utf8 bridge/tools/verify.py
python -X utf8 bridge/tools/query_integrated.py combined --deep
python -X utf8 tools/forest.py refresh --deep
python -X utf8 tools/bridge.py
python -X utf8 tools/semantic_lock.py
```

`semantic_lock.py --accept --note "具体复核原因"` 只用于明确记录新基线，不能当作消除漂移的证明。旧提交 `78bc059` 的历史审阅保持原样；本轮本地整合不改写其历史结论。
