# 第二轮六个任务的交付包（2026-10-23）

本目录是 `handoffs/next-round/README.md` 六项任务（P0/E1/E2/E3/M1/M2）在
`reviews/next-round-acceptance/REVIEW.md` 之后的**增量返修**交付包。

实现提交在六个分支上，本目录只放交付包（日志、哈希、复现入口）。实现提交里不含日志，
避免"日志记录自己的提交号"。交付包与本目录所在分支的对应关系如下：

| 任务 | 提交分支 | head（实现提交） | base | 本轮回合的性质 | 一句话 |
|---|---|---|---|---|---|
| P0 | `round2/p0` | `eff68757c84f3183bb0f8bed240a12dab2bc4039` | `484127185878e65b10795d20568bd3714eebc798` | 返修 | 判分只取冻结预期；bundle 与检出 HEAD 绑定；同 argv 去重；新增两条反例负测＋人工步骤不得 PASS；14/14 exit 0 |
| E1 | `round2/e1` | `24f42c645ba6ec61a693926d7956268e955a5b15` | `484127185878e65b10795d20568bd3714eebc798` | 返修 | 快速入口正常退出（exit 0，34.49 s）；总期限覆盖杀树（job object）；超时自证 124；72 项 discovery 全绿 |
| E2 | `round2/e2` | `7d3b66d25a5de9aaa4083d99b964fad65fa16ff4` | `484127185878e65b10795d20568bd3714eebc798` | **no-change** | 9 项 snapshot 成员规则用例逐条核实、22 项既有无回归；未改代码 |
| E3 | `round2/e3` | `6707684c8b6d7d521bb4cc803bc9a83ab0f0fb47` | `484127185878e65b10795d20568bd3714eebc798` | **no-change** | 6 项闭包保守化用例核实；36 项 pin 保留、proposal WITHHELD、removed=0 |
| M1 | `round2/m1` | `80967748f03e0545834d1cae3ffcfe4bcc7c4dac` | `063ce7bf12b5d94dae94da446982b4762435a8d1` | 返修（数学候选） | 保留 `hreal` 强前提版，新增一般 span 证书版 `restricted_ledger_span_criterion`；Lean 零 error/零 warning；公理 ⊆ {propext, Classical.choice, Quot.sound} |
| M2 | `round2/m2` | `e0b5294a3ef86674b14ecf18eb30949854752374` | `2a13a5b` | 返修（数学候选） | `hull_least_coordinateProduct`：对**任意坐标子集乘积**的最小性双向等价；旧的阈值盒版作为推论；基数与 2/3/4 例已证；四条 Lean 命令零诊断 |

## 复核方上一轮的意见与本次回应

`reviews/next-round-acceptance/REVIEW.md` 的结论（P0 FAIL / E1 INCOMPLETE / E2、E3 通过 /
M1、M2 陈述不足）逐条对应到上表的"本轮回合的性质"。每一项的 `SUMMARY.md` 写出**证明了什么**
与**尚未实例化什么**；`bundle.json` 给出完整哈希、命令、退出码、局限与未解决项。

## 本次没有做的事（不得据此升级状态）

- 没有运行任何新的 Lean 全仓构建，也没有做 VS Code 编辑器观察；因此 M1/M2 仍是 **candidate-only**，
  `fact_tree_admitted=false`，核心 GAP 全部保持 OPEN。
- 没有改 `fact-tree/registry.json`、pins、既有收据、既有冻结验收预期。
- E2/E3 本轮只做核实、未改代码；其分支 HEAD 与 REVIEW 记录的固定 HEAD 相同。

## 环境限制（复核方在自己机器上重放时不需要）

本机沙箱拒绝在 `tempfile.mkdtemp()` 的 `0o700` 目录内写文件（`WinError 5`）。因此：

- E1/E2/E3 的回放都用了「只把 `os.mkdir` 的 mode 参数丢掉」的 `sitecustomize` shim
  （E1 的 shim 在本目录 `e1/shim/`；E2 的 shim 未入库，见其 bundle 的 unresolved）；
- `TEMP`/`TMP` 指向工作树内的 `.tmp`；
- 路径含 `ü`，`test_tcb_manifest` 需要 `PYTHONIOENCODING=utf-8`。

在正常主机上（`D:/iut-wt/*` 工作树）不需要上述任何一条。

## 目录结构

```text
round2-2026-10-23/
├─ p0/  SUMMARY.md bundle.json logs/
├─ e1/  SUMMARY.md bundle.json logs/ shim/ (logs-superseded-e9ff362/ 为作废旧日志)
├─ e2/  SUMMARY.md bundle.json logs/
├─ e3/  SUMMARY.md bundle.json logs/ harness_e3_tests.py
├─ m1/  SUMMARY.md bundle.json logs/
└─ m2/  SUMMARY.md bundle.json logs/
```
