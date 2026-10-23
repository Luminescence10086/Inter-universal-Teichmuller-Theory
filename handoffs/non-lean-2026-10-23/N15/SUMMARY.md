# N15 文档、GAP、状态与候选依赖图对齐

2026-10-23。只读整理：**未运行 Lean/Lake/Lean 服务器，未打开编辑器，未改主线源码/配置/旧收据/GAP，未触碰 `fact-tree/registry.json`**。核心 GAP 仍 OPEN；本包不关闭任何 GAP。

## 交付

| 文件 | 内容 |
|---|---|
| `status.csv` | 37 行 × 19 列：T1–T4 / K4 / M1–M4 / W1–W12 / N01–N16 逐项索引 |
| `candidate-graph.json` | 37 节点、69 边（`counts` 分 `EXISTING_RECORD` / `PROPOSED`），每条边带证据路径，无无证据边 |
| `patch-proposal.md` | 12 条原文档改动建议（文件 + 行号 + 改法 + 理由），只提不改 |
| `make_N15.py` | 幂等生成器：只读扫描工作区全部 `delivery.json`，重跑字节一致（不写实时时钟） |

## 怎么读（不写死会漂移的计数）

工作区在构建期间仍在写入（N03、N06、N09、N13、N16 陆续落地），故本文件不写死总数，数字一律读 `status.csv`：

- `declared_status`：逐项自报状态（含 `NOT_DELIVERED` / `NO_DELIVERY_RECORD`，不替未交付项猜状态）；
- `cli_verified` / `editor_evidence`：两个平面分开记——自报的 CLI 通过、与 N14 的分级，互不替代；
- `hash_recheck_now`：主输出按盘上重算，本次运行全部 MATCH、0 项 DIFFERS（未交付项留空）。

## 三条判断

1. **编辑器证据比标签弱**：N14 已冻结的 21 行判词是 SUPPORTED 6 / INSUFFICIENT 6 / STALE 2 / MISSING 7，所以 `CLI_CHECKED_EDITOR_CHECKED` 的十项不能读成"该文件在编辑器里验过"。
2. **没有一份交付记录点名自己的 GAP 文件**（工作区全部 `delivery.json` 中 `GAP-core-*` 命中 0），故 `gap_ref` 是 N15 的路由**建议**（`gap_ref_basis` 逐条给依据），不是引自原件的 SOURCE_FACT。
3. **活工作区快照**：不按 HEAD 钉，而按每份记录自身 sha256 钉（`delivery_json_sha256` 列 / 图的 `source_record_sha256`）；某条记录被改后重跑即见，不必信任本文件的叙述。

## 边界

索引不构成数学验收、不构成 GAP 关闭、不构成编辑器准入；`declared_status` 抄自交付方自报并保留原词（含批外词表以外的 `CLI_CHECKED_*`），N15 不改写其含义。`native_iut_realized` 与 `fact_tree_admitted` 一律 false。
