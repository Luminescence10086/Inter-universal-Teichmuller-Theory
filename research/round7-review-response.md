# 对 78bc059 核验报告的逐项回应

日期：2026-10-20（Asia/Shanghai）。分支 `research/round6-bridge`。回应对象：
`reviews/78bc059b5b42/REVIEW.md`（F1–F4）与 `semantic-review.md`（S1–S6）。

本轮是在同一工作区中**两个并行会话**共同完成的：数学与工具的主体由本会话交付，
F2 的 schema-3 运行时绑定、`Integration.lean`、F4 的定义体门禁由另一会话实现；
两者都由本会话**独立重跑**过（命令与结果见下），不采信对方自述。

## 阻塞项

| 编号 | 处理 | 证据 | 状态 |
|---|---|---|---|
| F1 | 重新按字节保真策略入库 301 个被 CRLF→LF 归一的文件；新增清洁检出检查器，把**记录哈希**与 **HEAD blob** 比对（而不是与工作区比对） | `python bridges/check_clean_checkout.py` → `main 16/16, local 15/15, bridge 36/36 … clean checkout reproduces every recorded input` | ✅ 关闭 |
| F2 | bridge 准入改绑**真实导入闭包**：新增 `ImportsRuntime.lean`（module→olean 路径）与 `verify_integrated.py` 的运行时快照；receipt 升 `schema: 3` 并含 `runtime_sha256`；**schema-2 receipt 一律拒绝**（不足而非"过期"） | `python bridge/tools/verify.py` → `admitted=73, pending=0, receipt_valid=True`；`bridge/verification/checked-inputs.json` 记录运行时根与哈希 | ✅ 关闭 |
| F3 | 导出新鲜度改查**完整输入集**（含 `lean-toolchain`/`lakefile.toml`/`lake-manifest.json`/工具与 `@workspace/` 级工具），不再只筛 `.lean` | `tools/freshness.py` 被 `tools/bridge.py` 与锁工具共同调用；`bridge/verification/checked-inputs.json` 现含 36 个输入（含 5 个 `@workspace/` 工具项） | ✅ 关闭 |
| F4 | vendored 定义改由**类型 + 定义体源码文本**双门禁；旧的 `vendored definition type identical` 成功串已删除；新增 `tools/DefinitionBodies.lean` 与（并存）打印体锁 | `python tools/bridge.py` → `Contracts checked: 10; failures: 0; proof_transfer: false`；`bridges/facts.json` 增 `cross_toolchain_semantic_equivalence: false` | ✅ 关闭 |

负测（会失败才可信）：`bridge/tools/test_integrated_gate.py`、`tools/test_integration_audit.py`
覆盖运行时哈希改动 / schema-2 / 只给 3 个运行时产物 / 定义体被改（`∃→∀` 与一个参数下标）
四类场景；`tools/git_bytes.py` 在本次修复前确实以 30 个不匹配退出（含 `head=None` 的未提交件）。

## 语义与文案（S1–S6）

| 编号 | 处理 |
|---|---|
| S1 | 层梯方向全文改为**严格反单调**（`k ≤ m ⇒ layer m ⊆ layer k`；加宽朝更小指标）；`bridges/facts.json`/`index.md` 由 `tools/bridge.py` 重新生成，不再是手写残留 |
| S2 | `cost_exact` 只称**层间搬运恒等式**（带符号指数差）；`ScaleLedger` 模块注释显式声明未定义测度/体积/代价最优性；`research/round6-results.md`、`bridge/README.md` 同步 |
| S3 | **撤回**"混槽作用没有交换性"的概括，并把它变成定理：`Slots.lean` 新增 `mixingEquiv`（`(x₀,x₁)↦(2x₀+x₁, x₀+2x₁)`，det 3≠0 的 `Q_p` 线性自同构）与 `mixingEquiv_commutes_swap`（与槽位交换**交换**）、`mixingMap_not_slotwise`（确实不是逐槽作用）。审阅者的反例因此成为已编译内容，而不再是文档断言 |
| S4 | `relabel_trans` 注释改为"先 `τ` 再 `σ` 等于 `τ.trans σ`"，删去"反变"；报告表格同步 |
| S5 | 冻结结论从 `0` 推广到任意整数 `c`：新增 `frozen_isRectangular`；`Integration.lean` 另给出 `frozen_sigma_marginal_iff`，把"边际恰为 `{c}`"补成双向；模块注释改为"必要条件是**至多实现一个层**，选哪层自由" |
| S6 | p-adic log 表述改为"本 pin 上**没有找到可直接调用**的接口；本轮未形式化该像身份"；并更正事实：`Mathlib/NumberTheory/Padics/` 为 **12** 个源文件（原写 16） |

## 两个工程性决定

1. **不改 Lean 源以免作废 round-8 观察。** 本轮已取得真实的 schema-3 编辑器观察
   （`bridge/verification/vscode-observation-round8.txt`：5 份证明源的实际 VS Code
   可访问性树捕获，含 `No goals`；入口 `error 0 / warning 0 / information 146`）。
   receipt 绑定全部源文件哈希，因此**任何 Lean 编辑都会让它失效**。审阅者指出的
   `Merginal` 拼写（`Admissibility.lean:100,158`）属于纯注释，**故意推迟到下一轮编辑器观察**
   一起修，而不是为拼写牺牲本轮 73 条准入。
2. **锁工具归并。** `tools/semantic_lock.py`（语句+类型+定义体+公理，312 个常量）是本会话
   `tools/statement_lock.py`（语句+公理，188 条）的超集；语义锁为**规范入口**，
   `statement_lock.py` 与 `bridges/statement-lock.json` 作为历史保留，不再扩展。
3. **工具路径与 pin 的相互作用（本轮实测）。** schema-3 receipt 会把 `tools/*.{lean,py,json}`
   全量纳入输入集，因此**任何对 `tools/` 内文件的编辑都会作废一次真实编辑器观察**。
   本轮据此把 F1 检查器改放 `bridges/check_clean_checkout.py`（不被 pin），并把
   `tools/git_bytes.py` 恢复为与观察逐字节一致的版本。这是正确的绑定语义（工具决定证据），
   但代价是工具修复必须与下一次编辑器观察同批落地；若希望解耦，应在下一轮把 pin 收窄为
   **验证链实际调用的文件**（`verify_integrated.py`、`freshness.py`、`DefinitionBodies.lean`、
   `ImportsRuntime.lean`、`catalog.json`、`EditorCheck.lean`），而不是整个 `tools/` 目录。

## 当前可核验状态

```text
lake build（bridge）                2003 jobs，0 warning（--wfail）
bridge/tools/verify.py              admitted=73, pending=0, receipt_valid=True（schema 3）
tools/bridge.py                     Contracts checked: 10; failures: 0; proof_transfer: false
tools/semantic_lock.py              312 constants; changed=0, removed=0, added=0
tools/git_bytes.py                  main 16/16, local 15/15, bridge 36/36；0 mismatch
入口 CLI                            2 × 73 = 146 information、0 error、0 warning
```

## 仍未关闭

- `main`/`local-field` 两个既有工程的 receipt 仍是 schema 2（它们从未需要运行时绑定？
  不：它们本来就有；本轮未改其验证器，也未重跑其准入）。**本轮没有改动它们任何被追踪文件**。
- G01–G06 与 RI-01–08 全部 open；Corollary 3.12、abc 均未证明；未构造任何 IUT 对象。
- 并入 `main`、以及是否把 `bridge/` 写入根 `README.md`/`GAP.md`，仍待 Astra 复核后决定。
