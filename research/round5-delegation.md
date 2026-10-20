# 第五轮分工与验收边界

日期：2026-10-20（Asia/Shanghai）。按用户明确指定的模型分工执行：

| 角色 | 实际模型 | 子任务 | 交付物 |
|---|---|---|---|
| 重复性审计与复现 | `gpt-6-luna` | 第四轮深度查询、收据/诊断/公理核对，固定源码缓存；冻结候选后的构建及实际 VS Code 观察；收据绑定后的最终 CLI 门禁、图与汇总审计 | `round5-baseline-audit.md`、`round5-source-cache/manifest.json`、实际验收增量记录与最终门禁日志 |
| 结构证明探索 | `gpt-6-astra` | 从连续加法映射和有理数稠密性证明 ℚ_p 线性，连接实际理想过滤 | `LocalFieldAudit/ContinuousLinearity.lean`、`round5-continuous-linearity.md` |
| 真实联合实现探索 | `gpt-6-astra` | 审计 fullness、κ 代表、torsion orbit、同步与输出 region 的关系 | `round5-joint-realization.md`，全部保持未形式化候选 |
| 总体审阅与准入 | 父代理 | 审阅准确假设和范围，恢复编辑器面板并取得最终四项实际观察，绑定 receipt，复核 Luna 的最终门禁输出 | `round5-results.md`、最终编辑器观察及收据、事实图与汇总审计的复核 |

源码冻结前不进行准入。Luna 的基线深查完成后才放行 Astra 创建新 Lean 文件；Astra 的候选严格 CLI 检查通过并冻结后，才交给 Luna 整合导入/目录并执行构建与编辑器观察。没有多代理同时修改同一证明文件或同时控制 VS Code。

实际编辑器交接：Luna 完成入口及新证明的两项观察后，Filtration 复核遇到 Paperproof 空白面板，先保存增量记录并交还 UI。父代理恢复标准 Lean InfoView，重新取得四项完整观察并绑定收据；随后将最终 `verify.py`、forest 深查、查询和汇总审计交回 Luna。事件与恢复见根目录 `GAP-round5-editor.md`。

构造和研究候选不因模型名称获得认证。只有准确的 theorem、实际 Lean 检查、传递公理审计和 VS Code 零错误/零告警观察全部满足，才可进入 fact-tree。未形式化来源分析及开放 IUT 义务均不作为事实节点。
