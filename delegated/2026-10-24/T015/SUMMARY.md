# T015 · 当前倒推分支差异核对 —— SUMMARY

状态：`RESEARCH_ONLY`（来源/一致性核查，非数学成果；不授予 fact-tree 准入）
任务卡：`handoffs/agent-batch-2026-10-24/cards/T015.md`（sha256 `69200d7e…dc27`）
基线：主仓库 `8d60456043e30a3da79cc838d03a19b80675dc98`；`baseline.json` sha256 `e24e6801…26cf`（本次重算一致）

## 结论

**远端 `research/backward-paths` 与已审 commit `d3c5599` 是同一个提交：0 个新提交、空 diff、无需重做旧审查。**
该判断有两次独立取证：① `replay.ps1` 的历史实跑（18 次 git 调用全部 exit 0，`T015_REPLAY_PASS`）；
② 本次复核期间的**实时** `git ls-remote`（成功一次，取回同一 SHA）。此后网络中断，见「网络状态」。

| 项 | 值 |
|---|---|
| 远端 SHA（`git ls-remote` 实测，网络正常时） | `d3c5599668aa57c5c00244117abd26787fcd559e` |
| 远端跟踪 `origin/research/backward-paths` | `d3c5599668aa57c5c00244117abd26787fcd559e` |
| 本地 `research/backward-paths` | `d3c5599668aa57c5c00244117abd26787fcd559e` |
| 已审 SHA | `d3c5599668aa57c5c00244117abd26787fcd559e` |
| 关系 | **三者同一对象**；`for-each-ref --points-at` 仅此两条 ref 指向该提交 |
| 新提交（reviewed→origin） / （origin→reviewed） | **0 / 0** |
| `diff --stat` / 完整 `diff` | 空 / 0 字节 |
| 已审提交 tree | `731cdae8a42f46a13d38a47f3cd5be0d06bad580` |
| layer5 blob / 字节数 | `adc280bef846ca1e49b3a7b7071caaa725221797` / 9132 |
| 已审提交形状 | `1 file changed, 145 insertions(+)`；`diff-tree -r` = `A research/core-backward-2026-10-23/backward-paths-layer5-2026-10-23.md`（145/0） |
| `baseline..reviewed` | **4 files changed, 691 insertions(+)**（主文 215 / layer2 176 / layer34 155 / layer5 145） |

`8d60456` 是 `d3c5599` 的**祖先**（`merge-base --is-ancestor` exit=0），故 `d3c5599` = 基线 + 该分支 4 个提交。
注：非递归 `diff-tree --name-status` 只给出 `M research`（树条目折叠），`A <文件>` 取自加 `-r` 的权威输出，两者不矛盾。

## 网络状态（如实记录，含一次中断）

复核期内网络曾中断约 4 分钟，随后恢复；两端结果都已保留在 `logs/reverify-history.log`（8 条记录）：

| 阶段 | 实时 `git ls-remote` 结果 |
|---|---|
| 复核开始 | **成功**，取回 `d3c5599` |
| 14:11–14:14（5 次） | `exit 128`、`Failed to connect to github.com:443`；DNS 仍解析到 `20.205.243.166` 但 **TCP 443 不通**，每次超时约 21 s → `UNRESOLVED` |
| 14:15–14:16（3 次，恢复后） | **成功**，取回 `d3c5599` → `PASS` |

因此最终结果是 `PASS`：**网络恢复后重新实测，远端仍等于 `d3c5599`，仍无新提交**。中断期间的 `UNRESOLVED` 是当时网络状态，不是「远端已变动」的证据。

- `reverify.py` 把断言分成两类：**本地断言**（已审提交仍解析为同一对象、两条 ref 仍指向它、二者仍互等）始终执行并决定退出码；**网络断言**单独标注 `LIVE` / `UNRESOLVED`，不会被误判成失败——远端不可达不等于远端移动了。
- 若需再确认远端，重跑 `reverify.py`（需网络；加 `--skip-network` 可只跑本地断言）。

## 环境漂移披露（不影响本条结论）

`replay.ps1` 于 **2026-10-24T13:27** 运行时 HEAD = `8d60456`、tracked 脏文件 = 4。
本次复核时 HEAD 已前进到 **`aa4a320676f707770358cfc0afaa655f9b36662e`**（分支 `explore/correspondence`，祖先含 `8d60456`）。
脏文件数在复核期间由 4 变到 9 → 12 → 13，因为**主工作区正被并发占用**（其它 agent 在写 `delegated/2026-10-24/T003/` 与 `delegated/2026-10-24/_review/`）；本任务未触碰这些文件。

该漂移**不动摇** T015 靶心：T015 只问「远端分支 vs 已审 `d3c5599`」，二者都是 `refs/…/research/backward-paths`，不随工作区 HEAD 移动。
（`d3c5599` 不是现 HEAD 的祖先，exit=1——已审分支本就不在当前检出的主干上。）

## 本次实跑（只读）

无 fetch / checkout / reset / merge / 切分支。网络命令仅 `git ls-remote`（只联系；不写 ref、不写对象、不写 FETCH_HEAD），另有历史 `git fetch --dry-run`（`--dry-run` 同上）。
`pwsh` 不可用（本机仅 Windows PowerShell 5.1），`replay.ps1` 以 `powershell -NoProfile -File` 跑通并 exit 0；`reverify.py` / `build_delivery.py` 用 Python 3.14.5。

> `logs/_replay.trace.log` 每次运行会被 `Set-Content` 清空，因此只保留**最后一趟**：16 条 git 调用（13:27）。
> 另外 2 条网络命令取自更早一趟（13:13:28），其 `exit 0` 由 `logs/replay.full.log` 的 `[ OK ] … (git exit 0)` 佐证。
> `delivery.json` 用 `exit_code_source` 逐条标明每个退出码的来源文件，未混同。

## 官方预检 `check_delivery.py`

```
{"result": "PACKAGE_COMPLETE", "task_id": "T015", "reported_status": "RESEARCH_ONLY",
 "scope": "Material and hashes only. No reported command executed; mathematics, axioms, source semantics and editor observations remain unverified."}
```

调用：`python check_delivery.py --delivery delegated/2026-10-24/T015/delivery.json`，cwd = `handoffs/agent-batch-2026-10-24`，**exit 0**。
48 个 artifact、20 条 run；artifact 哈希与 `delivery.json` 自述经「写入→运行校验器→重写」迭代至**不动点**（第 2 轮收敛），自引用已闭合。

边界（按 PROTOCOL.md §Lean 与编辑器准入）：**`PACKAGE_COMPLETE` 只说明材料与哈希齐全，不是 Lean、编辑器或数学语义的通过**。本任务无 Lean 声明、无编辑器验收（`editor.performed=false`）。

## 未解决 / 不主张

1. 仅回答「远端分支 == 已审提交」这一事实问题；**不**复核也不背书 `d3c5599` 的数学内容（卡面要求「无新提交则不重复旧审查」）。
2. 远端其它 11 个 branch head 未核对（非 T015 靶心）。
3. 复核期内网络中断约 4 分钟（已恢复并重测通过）；若远端日后继续推进，需重跑 `reverify.py` 或 `replay.ps1`。
4. 主工作区 13 个 tracked 脏文件与并发写入未处理、未清理——按边界不得 reset/checkout 覆盖。
