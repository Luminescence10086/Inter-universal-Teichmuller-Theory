# CDS-A 引擎（在本仓库上的可运行实现）

四层 + 一横切的可执行实现：把"组织问题前置、运行期去中心、状态可回溯、错误在边上拦截"
变成代码里的**不变式**，而不是文档里的约定。

```text
cdsa/
  core.py     状态层（③）：单写者锁 + 追加式哈希链日志 + 版本快照；信封 schema + artifact 内容寻址
  engine.py   编译层（①）契约 DAG/预算；执行层（②）无状态执行器 + 并行；质量层（④）三色门禁、只读仲裁、局部回滚、全局终验
  specs/      目标 → 契约（示例：correspondence.json）
  tests/      21 项测试，逐层验证不变式
  runs/       事件日志、快照、日志、answer.json（可重放）
```

## 用法

```powershell
python -B -m cdsa run    --spec cdsa/specs/correspondence.json --repo . --run cdsa/runs/<name>
python -B -m cdsa run    ... --accept-handoffs          # 续跑：接手人工 handoff 节点
python -B -m cdsa verify --spec cdsa/specs/correspondence.json --repo . --run cdsa/runs/<name>
python -B -m unittest cdsa.tests.test_cdsa
```

`run` 打印每个节点的门禁颜色与是否准入；`verify` 从事件日志**重放**、重跑记录在案的命令证据、
校验哈希链与全部边条件，写出 `answer.json`，退出码 0 仅当 `PASS`。

## 四层如何落实（每条都是可执行检查）

| 层 | 机制 | 代码位置 | 不变式 |
|---|---|---|---|
| ① 编译 | 契约 DAG + 预算 | `engine.compile_spec` | 节点数/并行度在**编译期**锁死；未知字段（含 `chat`）直接拒；缺失 `dissent_template` 编译失败；环检测 |
| ② 执行 | 无状态执行器 | `engine.run_command/run_handoff` | 执行器之间不传递文本；只产出信封；大对象走 `artifactRef` |
| ③ 状态 | 单写者 + 哈希链 | `core.EventLog` | 无锁不可写；每行含 `prev`/`hash`，篡改即断链；快照=对日志的确定性折叠；可按检查点续跑 |
| ④ 质量 | 三色边门禁 | `engine.gate_envelope/arbitrate/verify_edge/final_answer` | 绿=解锁；黄=只读仲裁（只能用已落盘证据）；红=只回滚受影响闭包，**下游不再被调度** |
| 横切 | 反组织病 | 编译期 + 门禁 | 见下 |

横切规则的落点：

- **禁止自由协商**：信封字段固定，多一个字段即 `red`（conversation 不能搭车）。
- **匿名独立**：同层节点并行执行，互不看对方输出；只有声明为父边的节点才被解封。
- **强制异议**：`dissent` 为空即结构性无效（编译期要求 `dissent_template`，门禁要求非空）。
- **责任绑定**：每个信封带 `producer` / `spec_digest` / `version`。
- **共识门槛**：仲裁要求两种**独立证据类型**且置信度 ≥ 0.6，否则拒绝。
- **任务选择审计**：红节点重试达 3 次即记入 `audit` 并打印。
- **契约越界即红**：节点若写出 `allowed_paths` 之外的文件，门禁直接判红（执行器不能"顺手修上游"）。

## 一次真实运行（本仓库，非演示桩）

`cdsa/runs/demo-01`：目标=重新生成并独立核验语义对应台账，再记录一条带异议的人工综合 Claim。

| 节点 | 角色 | 执行的命令 | 门禁 |
|---|---|---|---|
| `N1-regen` | generate | `python -B bridges/correspondence_gen.py` | 绿（写入限于 `bridges/`） |
| `N2-verify` | verify | `python -B bridges/check_correspondence.py` | 绿（不写文件；与生成分离） |
| `N3-synthesis` | synthesise | 人工 handoff：Claim + 3 条证据 + 2 条异议 | 绿 |

`verify` 结果：`status: PASS`，`chain_ok: true`，`admitted_nodes` 三项齐全，
`command_evidence_rechecked: 2`（重跑了记录在案的命令证据）。事件日志 13 行，可完整重放。

## 建设过程中被真实跑出来的三个缺陷（已修，且都有回归测试）

1. 工作线程抛异常 → 主线程永远等结果 → **挂死**。现在执行器崩溃变成一个红色门禁信封。
2. `replay` 把"记录过的信封"当成"已准入"，导致红灯节点的下游仍被调度。现在区分
   `envelopes`（全部记录）与 `admitted`（门禁通过），调度只看 `admitted`。
3. `topo` 误用 DFS 后序（反拓扑序），并行调度顺序与测试期望不一致。现在显式反转。

## 负向验证（都实测过，可复现）

| 篡改 | 期望 | 实测 |
|---|---|---|
| 改 `logs/N1-regen.stdout.txt` 一个字节 | FAIL | `recorded command log no longer matches (hash mismatch)` |
| 改事件日志里某个**值**（`green`→`greeN`） | FAIL | `event log chain broken: hash mismatch at line 3` |
| 只重排日志 JSON 的空白 | PASS（不算篡改） | PASS——哈希链按 **canonical JSON** 计算，保护的是语义内容，不是字节布局 |
| 还原后重跑 | PASS | `status: PASS`，`git status -- cdsa` 干净 |

## 诚实边界

- 执行器是**命令**与**人工 handoff**，不是模型调用；引擎证明的是**流程完整性**，不是结论正确性。
- `confidence` 由生产者声明，未校准；仲裁是固定规则，不是判断力。
- 命令类证据只证明"该命令当时以该退出码运行、日志未被改动"，不证明命令自身的语义正确。
- `PASS` **不是**数学准入：本仓库的数学准入仍需实际 VS Code 观察与 receipt；本引擎不修改任何 pin、收据或 fact-tree。
- 引擎不联网、不写仓库之外、所有运行产物在 `cdsa/runs/<name>/`，可删可重放。
