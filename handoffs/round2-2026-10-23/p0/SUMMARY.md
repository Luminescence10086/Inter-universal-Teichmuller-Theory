# P0 返修：按冻结预期判定 + 绑定检出 HEAD

提交 `eff68757c84f3183bb0f8bed240a12dab2bc4039`（父 `8c78025`，冻结 base `484127185878e65b10795d20568bd3714eebc798`），只改 `audit/acceptance/`（3 文件）。

- ① 判定只取冻结 plan 的 `expected_exit`：实测 ≠ 预期即 `P0.expected_exit_mismatch`，与交付者自报 `outcome/exit_code` 无关；作者自报 FAIL/INCOMPLETE 凑不成整体 PASS。
- ② `validate_bundle` 要求 `HEAD == head_commit`（`P0.checked_out_head_mismatch`）、`source_tree_clean is true`（`P0.source_tree_identity`）、被跟踪文件无改动（`P0.source_tree_dirty`）；`source_tree_clean=null` 不再绕过。
- ③ 相同 argv/cwd/环境只实跑一次，其余 case 复用测量并保留映射（`executed_as` / `deduplicated`）；M1/M2 六条 Lean 命令去重为 2 次实际编译。
- ④ `manual: true` 恒为 `MANUAL_REQUIRED`，不进 PASS；新增用例 `P0.manual_step_never_pass` 守住。
- ⑤ 新增反例 `P0.failed_required_check_claimed_fail`（①）与 `P0.checked_out_head_mismatch`（②，含 HEAD 错位与脏工作树两段）。

工作树里未提交的 `run.py` 改动（临时文件替代管道、超时覆盖子进程清理）判为**正确予以保留**：实测父进程 0.08 s 返回（管道版会等孙进程，即 E1 的 595.7 s 症状）；超时路径关 Job 对象 → `taskkill /T /F` → 兜底 kill。已整体提交。

自测（`python -B audit/acceptance/tests/test_run.py`）：最终 **14/14，退出码 0，31.35 s**。控制实验：把 14c06a9 的旧 `run.py` 放入临时副本，两条新反例均 FAIL（旧代码判整体 PASS），证明反例有效。
期间两次失败已修：沙箱受限令牌下 `mkdtemp` 的 0o700 目录连创建者都不可写（改用默认模式自建临时根，退出码才正常）；归档用例落进本工作树内会向上发现 `.git`（改用 `GIT_CEILING_DIRECTORIES`）。

未解决：`.wt/p0/.tmp` 残留 5 个 0o700 目录（本人令牌无法读取或删除，未入提交，`--untracked-files=no` 不受影响，但 `git status` 会告警）；本工作树无 `handoffs/`，重放须显式 `--contract`。`lean_run`、`editor_run` 均未执行；数学准入仍为无，P0 待复核方重新冻结。
