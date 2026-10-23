# P0 验收启动器（薄层）

`run.py` 只做四件事：核对交付包元数据与冻结契约、核对真实 Git 差异与范围、按**冻结
allowlist** 重跑固定命令并捕获日志、输出 `verdict.json` 与一页摘要。它不做代码审查，
也不授予数学准入。

## 冻结输入

| 文件 | 作用 |
|---|---|
| `handoffs/next-round/contracts.json` | 任务、允许路径、必需用例 id；`sha256` 记录在 `plan.json` 的 `contract_sha256` |
| `audit/acceptance/plan.json` | **预期值与命令的权威来源**：每个 case id 的 argv、cwd、超时、预期退出码；`manual: true` 表示只能由复核者执行 |
| `audit/acceptance/probe.py` | 启动器自测用的固定探针（`ok` / `fail` / `slow`） |

`handoffs/` 属项目级输入，不在研究分支里：在评审工作树（`.wt/<task>`）中自测时，测试脚本
按 `P0_ACCEPTANCE_CONTRACT` → 本检出 → 上层项目目录 的顺序找 `contracts.json`，并先核对其摘要
是否等于 `plan.json` 的 `contract_sha256`（不一致直接报错退出，不进入用例）。

交付包**不能**提供自定义命令或预期值：argv 或 cwd 与 plan 不一致即 `P0.unapproved_command`；
`checks[]` 里多出必需集合之外的 id 同样被拒。

## 用法

```text
python -B audit/acceptance/run.py --bundle <外部交付包>/bundle.json --task E1
python -B audit/acceptance/run.py --bundle ... --repo <checkout> --contract ... --plan ...
python -B audit/acceptance/tests/test_run.py            # 14 项自测
python -B audit/acceptance/tests/test_run.py P0.timeout # 单项
```

退出码：`0` 仅当 verdict 为 `PASS`；`FAIL` 与 `INCOMPLETE` 均非零。启动器自身异常一律
`FAIL`，不会静默成功。

## 判定语义

- `PASS`：元数据、范围、重放三者一致。**不等于**代码审查通过，也**不等于**数学准入。
- `cwd` 由冻结 plan 固定**目录**，不固定写法：bundle 写绝对路径或相对路径皆可，但解析后必须
  等于冻结位置，否则 `P0.unapproved_command`。
- `changes[].sha256` 按 **HEAD blob 的原始字节**计算（等于干净检出写出的内容）；text 模式会
  把 `\r\n` 归一成 `\n`，因此不得用文本方式求摘要。
- bundle 顶层只允许模板字段，外加 plan 的 `allowed_bundle_extra_fields` 显式列出的**非可执行**
  元数据；未列出的未知字段一律拒。
- 必需用例之外的**补充检查**可以存在，但其程序前缀必须来自冻结 plan（含 `supplementary_programs`
  里按任务声明、用于重跑被测工具自身的项）；补充检查只校验日志摘要，不改变判定。
- `source_tree_clean` 只看**被跟踪**文件；未跟踪的临时文件记为提示（`P0.untracked_present`），
  不判失败——它们进不了提交，提交内容由范围检查负责。
- `INCOMPLETE`：超时、缺文件、无法执行、或含 `manual` 的复核者步骤尚未完成。
  这些情形**绝不**报告 `PASS`。
- 判定只取冻结 plan 的预期：实测退出码 ≠ `expected_exit` 即 `P0.expected_exit_mismatch`，
  与交付者自报的 `outcome`/`exit_code` 无关；作者自报 `FAIL`/`INCOMPLETE` 也不可能凑成整体 PASS。
- 重放绑定**检出 HEAD**：`HEAD` 必须等于 bundle 的 `head_commit`（`P0.checked_out_head_mismatch`），
  `source_tree_clean` 必须为 `true`（`P0.source_tree_identity`），且被跟踪文件无改动
  （`P0.source_tree_dirty`）——即被重跑的文件就是该 SHA 的提交内容。
- 相同**源码/环境/argv/cwd** 的命令只实际执行一次，其余 case 复用同一测量并保留 case 映射
  （`checks[].executed_as` / `deduplicated`）；因此多个数学 case 指向同一 Lean 文件时不会重复编译。
- `FAIL`：错提交号、范围越界、日志缺失或摘要不符、声称 PASS 但实测非零、
  必需用例缺失、冻结预期被改、未批准命令、缺 `.git` 上下文。

数学任务（M1/M2）的 `actual_vscode_observation` 在 plan 中标记 `manual`：启动器只能报告
"需要复核者重放"，不能代替实际 VS Code 观察。

## 已知限制

- 只做静态 allowlist 与重放一致性；不判断命令语义是否正确。
- 重放使用冻结 argv；plan 变更必须由复核者重新冻结（`P0.plan_contract_mismatch`）。
- 不覆盖 M 任务的 Lean 构建缓存身份；数学层仍以复核者实际 VS Code 与公理导出为准。
- 归档（无 `.git`）会 `P0.missing_git_context`：这是环境限制，不是生产缺陷。
- 子进程 stdout/stderr 写临时文件而非管道：孙进程继承管道句柄时 `communicate()` 会在直接子进程
  退出后继续等待（E1 实测约 595.7 秒仍未返回）。超时路径先关 Windows Job 对象（`KILL_ON_JOB_CLOSE`），
  再 `taskkill /T /F`（POSIX 用 `killpg`），最后兜底 `kill()`。
- 临时目录必须可写：沙箱内需把 `TEMP`/`TMP` 指到工作树内目录，否则临时文件与测试夹具都无法创建。

## 冻结流程（给复核者）

1. 审查 `run.py`、`plan.json`、`probe.py` 与本文件。
2. 确认 `plan.json` 的 `contract_sha256` 等于 `contracts.json` 的实际摘要。
3. 记录三份文件的 `sha256`，此后任何修改都视为新设计，需重新冻结。
