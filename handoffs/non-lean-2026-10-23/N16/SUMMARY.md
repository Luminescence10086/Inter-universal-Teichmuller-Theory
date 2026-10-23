# N16 — 统一交付包与快速验收工具

状态：`STATIC_COMPLETE`（工程校验工具；**不是**数学验收）

## 这是什么
`check_deliveries.py` 是本交付包的**独立静态检查入口**。它只回答四件事：
1. 每个 `Nxx/delivery.json` 是否满足 `handoffs/non-lean-task-catalog-2026-10-23.md` 第 3 节的契约（键、状态取值、布尔旗标全为 false）；
2. 声明为输入/输出的文件是否存在、路径是否在仓库内、**哈希是否与磁盘一致**（逐个重算，不采信自报）；
3. `SUMMARY.md` 是否声明且存在；
4. 是否出现被禁止的声明（编辑器过关、公理闭包审计、fact-tree 准入）。

它**不执行**交付包内任何脚本、不调用 Lean/Lake、不读环境钩子；退化为纯读盘 + JSON/CSV 校验。

## 运行
```powershell
py -3 handoffs\non-lean-2026-10-23\N16\check_deliveries.py                 # 全包
py -3 handoffs\non-lean-2026-10-23\N16\check_deliveries.py --only N01,N04  # 指定任务
py -3 handoffs\non-lean-2026-10-23\N16\check_deliveries.py --selftest --json-out report.json
```
退出码：`0` 全部干净、`1` 有发现、`2` 工具自身跑不起来。全包在固定环境下约 1–2 秒完成（只读盘，无外部进程）。

## 夹具自检（`--selftest` 的实际输出在 `report.json` 的 `selftest` 字段）
五类坏输入都被**拒绝**，且拒绝理由正是该夹具要触发的理由（`2026-10-23` 实测）：

| 夹具 | 结果 |
|---|---|
| `corrupt_hash`（改掉一个 output 的 sha256） | rejected：`outputs[0] hash mismatch …` |
| `missing_summary`（删掉 SUMMARY.md 与其条目） | rejected：`SUMMARY.md is declared but absent` |
| `status_vocabulary`（写成 `DONE`） | rejected：`status 'DONE' outside the vocabulary […]` |
| `path_escape`（`../../etc/passwd`） | rejected：`path escape` |
| `editor_claim`（声称编辑器过关） | rejected：`forbidden claim … claims an editor verdict` |

## 它不能做什么
- 不能判断数学真假、不能在 IUT 意义上验收任何命题；`report.json` 里明写 `not_a_math_check: true`。
- 不能替代人工抽查：它只保证"哈希与字段自洽"，不保证"摘要忠实"。
- 不修改任何交付、不重写 pin、不替作者补证据。

## 已知未覆盖
- CSV 内部语义（列含义、引文忠实性）不检查；那需要任务专属的 `verify_*.py`（例如 `N05/verify_N05.py`）。
- 不检查交付之间的一致性（重复、冲突）；那属于 N15 的索引层。
- 若某任务没有 `delivery.json`，只报一条 finding，不推断状态。
