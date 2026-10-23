# E2 — affected 覆盖 snapshot 文件集合变化（round2 / 2026-10-23）

- 工作树 `D:\Inter-universal Teichmüller Theory\.wt\e2`（分支 `round2/e2`）；base `48412718…c798` → head `7d3b66d2…6ff4`。
- 结论：**no-change**。9 项冻结用例已全部落在 `audit/tests/test_affected_snapshot_membership.py`，逐条核对后未发现缺口，未产生新提交（HEAD 仍为 `7d3b66d`）。
- 9 项 vs README：新增仅注释且未 import 的 `.lean`＝`new_lean_glob_member`；root/bridge glob 纳入的工具＝`new_workspace_tool`；`.vscode` 配置＝`new_vscode_config`；改名前→规则外进入＝`rename_into_scope`；规则内移出＝`rename_out_of_scope`；删旧输入＝`delete_pinned_input`；两个正常对照＝`documentation_control` / `out_of_scope_control`；38+24+73 与 `nodes_invalidated` 分离＝`distinct_node_counts`。
- 真实生产函数：fixture 复制 `tools/verify.py`、`local-field/tools/verify.py`、`bridge/tools/verify_integrated.py` 后 import 并调用 `snapshot` / `project_snapshot` / `dependency_snapshot`；每例先用该函数独立证明真规则增/失成员，再断言 planner 输出。
- 断言方向：新成员→`VOID` 且 `membership.added` 点名；规则外/文档→`INTACT`（`assert_status` 强制 probe 为 `decided`，无法空过）；规则内移出靠记录 pin 判 `VOID` 且 `added` 必须为 `[]`；snapshot 抛错时若有 pin 记 `VOID`，无 pin 则 `UNKNOWN`（`E2.extra.*` 覆盖）。
- 运行 1（冻结 argv）：`python -B audit/tests/test_affected_snapshot_membership.py <9 case ids>` → exit **0**，9/9 PASS，**15.89 s**。
- 运行 2（既有回归）：`python -B audit/tests/test_affected.py` → exit **0**，22 tests OK，26.09 s，无回归。
- 环境坑（复跑必读）：本沙箱下 `tempfile.mkdtemp` 的 `0o700` 目录不继承 sandbox 组 ACE——只把 `TEMP/TMP` 指到工作树 `.tmp` **不够**，会 9/9 `PermissionError [WinError 5]`；本次用运行时 `PYTHONPATH=<.tmp>\shim` 的 `sitecustomize.py` 把 `os.mkdir` 的 mode 强制为 `0o777`（未入仓库）。
- 未解决：① 上述 shim 是环境绕行，未随交付固化（建议复核方在正常主机上直接重放）；② `E2.extra.*` 三个非冻结用例未跑；③ 未做 Lean/编辑器观察（E2 为工程任务，不适用）。
