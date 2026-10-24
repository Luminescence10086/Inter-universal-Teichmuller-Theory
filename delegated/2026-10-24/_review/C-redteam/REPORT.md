# 独立审查官 C（压力测试 / 红队）审查报告

| 项 | 值 |
|---|---|
| 审查性质 | **只读**压力测试 / 红队（目标是把交付弄坏，看门禁能不能拦住） |
| 审查范围 | `delegated/2026-10-24/` 下已出现的 8 个交付目录 + `handoffs/agent-batch-2026-10-24/check_delivery.py` |
| 取证窗口 | 2026-10-24 **13:09 → 13:32**（+08:00）。**交付在此期间持续变化**，见 §9 |
| 隔离方式 | 全部坏输入只在 `%TEMP%\c-redteam\` 制造；仓库内除 §3 的 T015 重放外**零写入** |
| 复现脚本 | `%TEMP%\c-redteam\redteam.py`（38 例）、`redteam2.py`（8 例）；结果 `redteam-results.json`、`redteam-round2.json` |
| 判定用词 | `HELD`＝门禁拦住 / `BYPASSED`＝绕过（附最小复现）/ `NOT_APPLICABLE`＝该路不可用 |

---

## 0. 一页结论

**一句话：`check_delivery.py` 是一台合格的「材料完整性」校验器，不是「证据真实性／结论强度」校验器。它守得住"文件有没有被改过"，守不住"这个通过是不是真的"。**

三部分共 **104 例实测**：`HELD 61` / `BYPASSED 42` / `NOT_APPLICABLE 1`。

**最严重的一条（贯穿全部三轮，且在四份真实交付上 4/4 复现）：`exit_code` 纯属自报，日志内容零解析。**

- 把失败改成 0（隐瞒）**和**把成功改成 1（伪造失败）**都返回 `PACKAGE_COMPLETE`**；
- 在四份真实交付（T003/T008/T066/T097）上做同样篡改，**全部放行，无一例外**；
- 在 T008 的真实交付上，把唯一那条**如实登记的失败**（`discarded_attempt`, `exit_code: 1`）改成 `0`，预检器输出**与改之前逐字相同**。

**换句话说：门禁对"诚实披露失败"与"隐瞒失败"给出完全一样的评语。它恰好把激励放反了。**

第二条同级问题：**`sorry` / `sorryAx` / 公理白名单完全不检查**——我用 T049 自己产出的、未改一字节的真实证据（日志里含 3 处 `declaration uses sorry`、12 处 `sorryAx`）组装 `delivery.json`，预检器照样 `PACKAGE_COMPLETE`。

第三条（父线程重点，已实测证实）：**预检器没有任何机制能发现"标错强度"**。T008 的 `18 constructed / 5 hypothesis / 6 with extra hypotheses` 改成 `23 constructed / 0 hypothesis / 无条件`、并加上"closes the IUT core gap"，**exit=0，毫无反应**。

### 三条最该被记住的话

1. **改一个字节它一定拒绝**（8/8 实测），**改 exit_code 它一定放行**（8/8 实测）。
2. **`PACKAGE_COMPLETE` 只证明"材料齐、哈希对"**，不证明数学、不证明公理、不证明命令真的跑过、不证明结论强度标对了。它的 `scope` 字段其实写得很诚实，**问题是流程上极易被读成"通过验收"**。
3. **T008 是材料层最硬、且唯一如实披露失败的一份，而它与"把它的诚实改掉之后的它"拿到的评语完全相同。** 门禁目前无法区分诚实与隐瞒。

---

### 分节索引

| 部分 | 内容 | 判定 |
|---|---|---|
| §1 | 六类坏输入（自建 fixture） | (a)(d)(e) HELD；(b)(c)(f) 部分 BYPASSED |
| §2 | 空构建检测 | `lake build` 无参实测 **exit=0**（"Nothing to build"），2a/2b/3 BYPASSED；(2c) HELD |
| §3 | 证据可回放性 | T015 replay **REPLAYABLE/PASS**；其余 NOT_REPLAYABLE |
| §4 | 时间/一致性 | 预检器**无时间维度**，mtime 攻击 BYPASSED |
| §5 | 洗白路径 8 例 | **8/8 BYPASSED** |
| **§C** | **以真实 T008 为靶（六类 + 强度 + provenance + replay）** | 强度错标 **无感**；T008 Lean replay **PASS** |
| **§D** | **四份真实交付复查 + 真破坏** | 一字节篡改 **8/8 HELD**；exit_code／删 runs **12/12 BYPASSED** |

---

## 0.1 旧版一页结论（保留：T049 真实证据实验，仍有效）

**`check_delivery.py` 对 `sorry` / `sorryAx` 完全无感——而本轮就有一个交付把 `sorryAx` 写在自己的日志里。**

我用 **T049 自己产出的、未改一个字节的真实证据**组装了一份 `delivery.json`（`status=RESEARCH_ONLY`，`argv` 就是它日志里的 `lake build T049`，附上真实的 `logs/build01.log`），预检器给出：

```
{"result": "PACKAGE_COMPLETE", "task_id": "T049", "reported_status": "RESEARCH_ONLY",
 "scope": "Material and hashes only. No reported command executed; ..."}
exit=0
```

而这份被盖章的日志里实际写着：

```
$ Select-String T049\logs\build01.log -Pattern "declaration uses .sorry."  -> 3 处
$ Select-String T049\logs\build01.log -Pattern "sorryAx"                  -> 12 处
src\T049\FinitePlaceNorm.lean:95:8: error: declaration uses `sorry`
src\T049\FinitePlaceNorm.lean:102:8: error: declaration uses `sorry`
src\T049\FinitePlaceNorm.lean:131:8: error: declaration uses `sorry`
'T049.norm_pos' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'T049.norm_le_one_iff_mem_adicIntegers' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
...
```

PROTOCOL「Lean 与编辑器准入」白纸黑字写「不允许 sorry、admit 或自加公理」「可接受基线为 propext / Classical.choice / Quot.sound」——**这条在交付物里被违反，而门禁原样放行，还回了一句 PACKAGE_COMPLETE。**

其余两条同级问题：

1. **`exit_code` 是纯自报值，且日志内容零解析。** T049 的 `build01.log` 通篇是 `error: ...` 与 `error: build failed` 语义（73 行、16 条 error），而我在 `delivery.json` 里写 `exit_code: 0` 即通过。**更强的证明见 §3.2**：在 T008 的**真实**交付上，把"诚实披露的 `exit_code: 1`"悄悄改成 `0`，预检器给出的判定**一字不差**。
2. **截至 13:34，真实 `delivery.json` 只出现 1 份（T008）**，其余 7 个目录仍无。把预检器指向它们，**7/7 exit=2**：

```
$ python check_delivery.py --delivery delegated/2026-10-24/T002/delivery.json
{"result": "PACKAGE_INCOMPLETE", "error": "...No such file or directory: '...T002\\delivery.json'"}
  ^ T002 exit=2   (T003/T015/T021/T049/T065/T097 同，均 exit=2)
$ python check_delivery.py --delivery delegated/2026-10-24/T008/delivery.json
{"result": "PACKAGE_COMPLETE", "task_id": "T008", "reported_status": "RESEARCH_ONLY", ...}   exit=0
```
```

**判定分布**（46 例）：`HELD 21` / `BYPASSED 22` / `NOT_APPLICABLE 1` / 对照 2。明细见文末附录。

---

## 1. 预检器对抗测试（任务书六类坏输入）

沙箱：`check_delivery.py + tasks.json + baseline.json + source-seed.{json,zip} + cards/` 复制到 `%TEMP%\c-redteam\cat`，副本先自证可用：

```
$ python cat/check_delivery.py --catalog cat --check-catalog
{"result": "CATALOG_COMPLETE", "tasks": 128, ...}   exit=0
$ python cat/check_delivery.py --self-test
{"result": "PREFLIGHT_SELF_TEST_OK", "synthetic_rejections":
 ["bad_hash","missing_file","stale_card","escape_path","false_lean_candidate"], ...}   exit=0
```

先建一份**诚实自洽**的 fixture（T113，RESEARCH_ONLY，源码/日志/公理齐全）作阳性对照，确认沙箱公平：

```
[PASS] SANITY honest RESEARCH_ONLY fixture      expect=ACCEPTED got=ACCEPTED exit=0
```

### (a) 改一个字节使 SHA 不匹配 — **HELD**

```
[PASS] (a) 1-byte tamper, stale declared SHA   REJECTED exit=2
       error: artifact SHA mismatch: logs/build.stdout.log
```
最小复现：`logs/build.stdout.log` 末尾追加 1 字节，`artifacts[3].sha256` 不动 → exit 2。

**加强版被绕过**（同时改内容与哈希，哈希门禁的固有界限）：

```
[(a+) 1-byte tamper + attacker refreshes hash  ACCEPTED exit=0
```
判定：**(a) 纯篡改 HELD；(a+) BYPASSED**。SHA 只能证明"与我声明的一致"，不能证明"是我跑出来的"；真正能关门的内容一致性检查在 (c)、(f) 未实现。

### (b) 删掉 `commands_run` — **BYPASSED（RESEARCH_ONLY）/ HELD（candidate）**

```
[(b) delete commands_run (runs) entirely        ACCEPTED exit=0
[(b+) runs=[] but status=CLI_CANDIDATE         REJECTED exit=2  "declaration not bound to a recorded Lean run"
[(b) drop run.stdout pointer                   REJECTED exit=2  "file path must be a nonempty string"
```
`runs` 只在 `CLI_CANDIDATE`/`EDITOR_CANDIDATE` 下被强约束（`check_delivery.py:143-144,155-161`）。**只要把 `status` 写成 `RESEARCH_ONLY`，就可以完全不记录 `argv/cwd/exit_code/duration/stdout/stderr`，而 `PACKAGE_COMPLETE` 照发。**
与 PROTOCOL「最小交付」第 3 项（必须列 argv/cwd/退出码/耗时/完整 stdout/stderr）直接冲突。

### (c) `exit_code` 改 0 但日志留非零证据 — **BYPASSED（门禁总闸）**

```
[(c) exit_code=0 while stderr holds a Lean error   ACCEPTED exit=0
[(c) exit_code as string "0"                       REJECTED exit=2  "actual run exit_code required"
[(c) exit_code as JSON true                        REJECTED exit=2  "actual run exit_code required"
[(t) stdout has '✖'/'error:' yet exit_code=0      ACCEPTED exit=0
[(t) CLI_CANDIDATE with exit_code=1               REJECTED exit=2  "candidate records a nonzero exit"
```
类型检查严（`type(run.get("exit_code")) is int`，line 132），但**全文没有任何地方读日志内容**。最小复现：日志写入 `error: unknown identifier 'foo'` 并刷新其哈希 → 记 `exit_code: 0`、`status: RESEARCH_ONLY` → `PACKAGE_COMPLETE`。

**这不是理论风险**：§0 已用 T049 的真实日志（16 条 error）实测放行。只要交付方谎报 `exit_code=0`，**整份预检器会为一份失败的构建背书**，其余门禁因此全部失去意义——因为所有证据都由同一方自报。

### (d) 路径逃逸（`../../../etc`） — **HELD**

```
[(d) summary_file escape ../../../etc/passwd          REJECTED exit=2  "path escapes delivery: ../../../etc/passwd"
[(d) artifacts[0].path escapes delivery root          REJECTED exit=2  "path escapes delivery: ../../../../Windows/win.ini"
[(d) absolute Windows path in artifacts               REJECTED exit=2  "bundle file must be relative: C:/Windows/win.ini"
```
另测 **junction（目录联结，不需管理员权限）指向外部目录**，`resolve()` 落在根外，同样被拦：

```
$ cmd /c mklink /J fixtures\T113-RESEARCH_ONLY\j outside_dir
resolve(): C:\Users\...\c-redteam\outside_dir\secret.txt      is_relative_to(root): False
$ python check_delivery.py --delivery .../delivery.json
{"result": "PACKAGE_INCOMPLETE", "error": "path escapes delivery: j/secret.txt"}   exit=2
```
判定：**HELD**（`local_file()` 的 `resolve()`＋`is_relative_to`，line 46-47 有效）。

- 附带**误报**（对交付方偏严，非安全缺陷）：`sub/../../SUMMARY.md` 解析后仍在根内却被一律拒绝。
- **`NOT_APPLICABLE`**：符号链接逃逸——本机 `mklink` 报 `WinError 1314`（无 `SeCreateSymbolicLink` 权限），该用例从未真正执行，其结果无效，已作废、不计入统计。

### (e) 状态写成白名单外的值 — **HELD（但可旁路）**

```
(e) status='VERIFIED' / 'PASS' / 'CLEAN' / 'DONE' / 'VERIFIED_LOCAL_SHARD' / 'cli_candidate' / "CLI_CANDIDATE "
    -> 全部 REJECTED exit=2  "invalid status"
```
判定：**HELD**，白名单＋精确匹配干净（line 16, 102）。
**但白名单只管 `status` 一个字段，自由文本完全不受约束**：

```
[(t) free-text research_result='VERIFIED'         ACCEPTED exit=0
[L5] 'Corollary 3.12 established' in free text     ACCEPTED exit=0
```
最小复现：`status` 保持 `RESEARCH_ONLY`，另加 `"research_result": "THEOREM PROVED. Corollary 3.12 established."` → exit 0。**BYPASSED（旁路）**。

### (f) 声明 `sorry` 却标 CLEAN — **BYPASSED（4/4），且已在真实交付中复现**

```
[(f)  source contains 'sorry', status RESEARCH_ONLY             ACCEPTED exit=0
[(f+) 'sorry' + status CLI_CANDIDATE (CLEAN claim)             ACCEPTED exit=0
[(f+) axioms log lists sorryAx                                 ACCEPTED exit=0
[(f)  'declaration uses sorry' in stdout log                   ACCEPTED exit=0
```
最小复现：诚实 fixture → `Proof.lean` 改成 `theorem t113_ok : True := by sorry` → 刷新三处 sha → **`PACKAGE_COMPLETE`**。
连 `axioms_log` 写 `[propext, sorryAx]` 也照过：`registered()` 只校验"文件被登记且哈希一致"，**从不解析内容**（line 116-119, 154）。

**真实复现（本报告最强证据）**：§0 的 T049 实验——用交付方自己的 9060 字节 `build01.log`（含 3 处 `declaration uses sorry`、12 处 `sorryAx`）→ `PACKAGE_COMPLETE`，exit 0。

---

## 2. 空构建检测（`lake build` 无参记成通过）

**先实测 Lean 侧事实**（与交付同钉版 `leanprover/lean4:v4.34.0-rc2`，临时 MWE）：

```
$ lake build            # lakefile 未声明 lean_lib / defaultTargets
warning: no targets specified and no default targets configured
  Note: This will be an error in a future version of Lake.
Nothing to build.
[A] exit=0                              <-- 编译 0 个目标，退出码仍是 0（成功）

$ lake env lean -DwarningAsError=true   # 有严格 flag，无目标文件
lake : Expected exactly one file name
[B] exit=1
```
**空构建不会留在退出码里**，只留一行人类可读文本；因此这道门唯一的可检查线索在**日志文本**里，而预检器不读日志文本。

```
[(2a) argv=['lake','build'] + 'no targets specified'   ACCEPTED exit=0
[(2b) lean w/ strict flag but NO target file          ACCEPTED exit=0
[(2c) CLI_CANDIDATE via bare 'lake build'             REJECTED exit=2  "strict Lean command not recorded"
[(3)  run exit_code=1, nonempty-looking stdout        ACCEPTED exit=0
```
- **(2c) HELD**：`CLI_CANDIDATE`/`EDITOR_CANDIDATE` 且 `proof_mode == LEAN_CANDIDATE` 时，line 160 强制要求带 `-DwarningAsError=true` 的 lean run，裸 `lake build` 过不了。
- **(2b) BYPASSED**：写成 `["lake","env","lean","-DwarningAsError=true"]`（**不带任何文件名**）即可满足 line 160——实测该命令真实退出码为 **1**，但 `exit_code` 是自报值（§1(c)），照样通过。
- **(2a)(3) BYPASSED**：`RESEARCH_ONLY` 下 `runs` 无语义约束。

**本轮真实交付中 `no targets specified` 零命中**（grep 全仓仅 Reviewer A 的两份文档 4 处命中）。**但这不等于空构建已被识破——只是本轮没人这么做。**

### 2.1 真实日志里更值得注意的反向现象

- **T049** `logs/build01.log`（9060B，13:30:12）：是 `lake build T049` 的真实输出，但**是失败输出**——16 条 error、3 处 `declaration uses sorry`、末尾 `error: build failed`。
- **T021** `logs/build-snapshot-ThetaGermTransport.log`：全程 `lake build Boundary.ThetaGermTransport`（目标显式，**这点合规**），但该文件在 13:21→13:32 之间被**反复覆盖**，内容从部分成功 → `✖ Corestriction` + `error: Lean exited with code 4294967295` → 全长 144 字节 → 13:32:10 又变成 `✖ Boundary.Frontier` + `unknown module prefix 'CohomologyReflection'` + `lake : error: build failed`（6302B）。**同一份"证据"文件在同一任务内被覆盖三次，每次都对应一次失败的构建尝试。**

---

## 3. 证据可回放性

现实前提：8 个交付目录里**没有任何一个记录了结构化 `commands_run`**（0 份 `delivery.json`）；`replay.ps1` 有 T015 与 T008 两份（T008 的于 13:31:17 才出现）。

### #1 T015 `replay.ps1` — **REPLAYABLE，且 PASS**

脚本自述的解释器在本机**不存在**：

```
$ pwsh -NoProfile -File delegated\2026-10-24\T015\replay.ps1 -SkipNetwork
pwsh : The term 'pwsh' is not recognized ...
$ $PSVersionTable.PSVersion  -> 5.1.26100.9711      (Get-Command pwsh -> 空)
```
按其头部自述的降级路径改用 5.1：

```
$ powershell -NoProfile -ExecutionPolicy Bypass -File delegated\2026-10-24\T015\replay.ps1 -SkipNetwork
[ OK ] baseline.json sha256 = e24e6801...
[ OK ] HEAD = 8d604560...     [ OK ] reviewed commit = d3c55996...
[ OK ] reviewed tree = 731cdae8...   [ OK ] layer5 blob size = 9132
[ SKIP ] network checks (ls-remote / fetch --dry-run)
[ OK ] new commits remote-side = 0    [ OK ] new commits reviewed-side = 0
[ OK ] reviewed commit = 1 file changed, 145 insertions(+)   [ OK ] tracked dirty file count = 4
T015_REPLAY_PASS: remote research/backward-paths == d3c5599668aa57c5c00244117abd26787fcd559e
[replay exit=0]
```
**重跑前后对 `logs/` 39 个文件逐一 SHA256 比对**：38 个字节不变，唯一变化是 `_replay.trace.log`（脚本预期覆盖的自身 trace）。**只读声明成立、可回放性成立。** 判定 **REPLAYABLE / PASS**。

### #2 其余任务 — **NOT_REPLAYABLE**

- **T049**：命令行唯一出处是 13:30:12 版日志里被 PowerShell 错误信息截断的
  `+ ... $log="logs\build01.log"; $t0=Get-Date; & lake build T049 2>&1 | Tee-O ...`
  无 `cwd`、无退出码记录；且该日志内容是**失败**。判定 **NOT_REPLAYABLE**。
- **T021**：日志含 trace 行，**目标文件显式**（`.../Boundary/Frontier.lean`，合规）；但无 `cwd`、无退出码，且 trace 对应**失败**目标，且原日志已被覆盖（§2.1）。判定 **NOT_REPLAYABLE**。
- **T002/T003/T065/T097**：目录内无可执行 replay（仅 `.tmp/*.py`、日志、json），无结构化 argv → **NOT_REPLAYABLE**。
- **T008**：13:31:17 出现 `replay.ps1`，但**我未运行**——它依赖 `candidates/core-kummer` 且会与现场正在运行的 `lake build` 争用（§9）。按"未重放"记，不判失败。

### 3.1 T008 证据的编码问题（机械复核会卡死）

`T008\logs\probe.stdout.log`（29752B）是 **UTF-16LE**：

```
bytes 29752   has NUL: True   NUL count: 14322
decodes as UTF-8: NO -> 'utf-8' codec can't decode byte 0xff in position 0
$ read(...) -> Error: binary file
```
同一目录的 `attempt1.stdout.log` 却是 UTF-8。**同一交付内编码不一致，会让任何"读日志做核验"的自动门禁直接失败或读出乱码**。按 UTF-16 正确解码后内容本身是干净的：203 行、**0 error / 0 warning / 0 sorry**、11 条 `#print axioms` 全部只含 `propext / Classical.choice / Quot.sound`（我在 §9 逐条核过）。

判定汇总：**1 条 REPLAYABLE（T015，PASS）；7 条 NOT_REPLAYABLE / 未重放**。

### 3.2 对**真实交付物**的定向攻击（T008，最有力的单例）

13:33:57 出现第一份真实 `delivery.json`（T008，16960B）。它**自证通过**：

```
$ python check_delivery.py --delivery delegated/2026-10-24/T008/delivery.json
{"result": "PACKAGE_COMPLETE", "task_id": "T008", "reported_status": "RESEARCH_ONLY", ...}   exit=0
```

我先**独立重算**它登记的 14 份产物哈希（不采信其自报）：

```
=== INDEPENDENT hash recompute of all 14 artifacts ===
  ok   SUMMARY.md / ARROW-TABLE.md / GAP.md / replay.ps1 / probe/T008Probe.lean
  ok   logs/probe.stdout.log / probe.stderr.log / replay.stdout.log / replay.stderr.log
  ok   logs/replay.console.log / attempt1.stdout.log / attempt1.stderr.log
  ok   logs/check_delivery.stdout.log / check_delivery.stderr.log
mismatches: 0
```

**14/14 哈希实算全中，0 失配** —— 这份交付的材料层是**干净的**，我没有任何材料层指控。

它的 `runs` 里有一条**诚实披露的失败**：

```json
{"kind": "discarded_attempt", "exit_code": 1, "duration_seconds": 52.85,
 "argv": ["lake","env","lean","-DwarningAsError=true","<attempt-1 T008Probe.lean, since replaced>"],
 "stdout": "logs/attempt1.stdout.log", "stderr": "logs/attempt1.stderr.log", "inputs": []}
```

现在做定向攻击：**只把这一个 `exit_code` 从 1 改成 0**，其余一字不动，跑真预检器：

```
BASELINE (unmodified copy of the real delivery):
   {"result": "PACKAGE_COMPLETE", "task_id": "T008", "reported_status": "RESEARCH_ONLY", ...}  exit 0
AFTER flipping discarded-attempt exit 1 -> 0:
   {"result": "PACKAGE_COMPLETE", "task_id": "T008", "reported_status": "RESEARCH_ONLY", ...}  exit 0
```

**两次判定一字不差。** 也就是说：**交付方如实披露失败，与悄悄抹掉失败，在门禁眼里没有任何区别。** 这不只是"可以被绕过"，而是**门禁对诚实没有任何回报、对隐瞒没有任何惩罚**——它恰好把激励放反了。

> 这一条的杀伤力比 §0 的 T049 实验更大：T049 是我自建的 `delivery.json`，而这里是**真实交付物上的最小单点改动**。T008 之所以被选中，正因为它是最诚实的一份——门禁对它和对一份伪造件给出同样的 `PACKAGE_COMPLETE`。

---

## 4. 时间 / 一致性

### 4.1 日志早于源码 — **HELD（一致）**

T015 是唯一能真正对时间的任务，且**对得上**：trace 各步 exit=0，重放重算的 HEAD/commit/tree/blob 全等于声明值，`logs/` 重放后哈希不变。

### 4.2 源码晚于其日志 — **BYPASSED（预检器无时间维度）**

```
[(4) source mtime 2h AFTER its build log        ACCEPTED exit=0
```
最小复现：日志 mtime 设为 T0、源码设为 T0+7200，**其余（含哈希）自洽** → `PACKAGE_COMPLETE`。
预检器**不读 mtime、不解析 duration 与日志时间序**（`duration_seconds` 只校验 `>=0` 且有限，line 133-135）。PROTOCOL「源码改动后，旧日志不再证明新版本」**完全没有对应门禁**。

### 4.3 真实交付里的时间/状态矛盾（现场实测）

| # | 现场事实 | 问题 |
|---|---|---|
| 1 | `T008\logs\attempt1.stdout.log` **13:20:35** → `T008\probe\T008Probe.lean` **13:26:01** | 现存源码比其失败日志晚 5.5 分钟；**该日志证明的那版源码已不存在**，且日志未标作废。作者在源码注释里自述"attempt 1 … was discarded, not repaired"，属**诚实披露**，但日志本身仍是悬空证据 |
| 2 | `T021\logs\...\log` 13:21→13:32 **被覆盖 3 次**（详见 §2.1） | 中途的失败记录（`Corestriction` 的 `error: Lean exited with code 4294967295`）**已被后一次运行覆盖，不可回溯** |
| 3 | `T049` 13:24–13:27 期间有 `.lake/`（13 文件），13:32 时**已消失**（现 7 文件，`.lake` 不存在） | 交付方中途清理了构建产物；`build01.log` 是清理后留下的**失败**日志 |
| 4 | `T049\logs\build01.log` mtime **13:30:12** 晚于 `src\T049\FinitePlaceNorm.lean` **13:26:53** | 时间序**自洽**（先改源、后构建），此处**无矛盾** |
| 5 | `T021` 的 `Corestriction` 目标曾报 `failed to read file '...Kan\Adjunction.olean.private'`（13:22 采集） | 构建环境本身曾损坏；该错误随后被覆盖 |

### 4.4 Reviewer A 报告与被审对象的时间矛盾

`_review/A-evidence/ROLLUP.md` 第 5 行写「审查时刻（UTC）：2026-10-24 ~04:1x」，按 +08:00 折算是**北京 12:1x**。但：

- 交接包自身 mtime 为 **12:50–12:53**（`PROTOCOL.md` 12:50:55、`check_delivery.py` 12:52:16、`validation.json` 12:53:40）；
- 最早交付目录 **13:09:05**（T002）。

→ **A 的"审查时刻"早于被审查对象存在约 40 分钟。** 我不断言其造假（正文细节与 13:13 前后产物高度吻合，可能只是 UTC 笔误），但**以文件声明时间戳为准则该报告不成立**；C 类本就不采信自报时点。另：A 的 ROLLUP 称「`Get-ChildItem` 仅返回 T002 一个目录」，而该文件 mtime 为 **13:13:50**，我实测 13:13:09 时 T002/T008/T015 已存在。此项交父线程裁断。

---

## 5. 第二轮：现实可行的"洗白"路径（8/8 全过）

| 例 | 手法（仅临时目录） | 结果 |
|---|---|---|
| L1 | `replay_file` 指向 `SUMMARY.md`（**根本没有 replay 脚本**） | ACCEPTED |
| L2 | `summary_file` 指向 3 字节日志（**没有摘要**） | ACCEPTED |
| L3 | 把 **T021 的真实构建日志**当 T113 的证据提交 | ACCEPTED |
| L4 | 声明写 `theorem x : True := trivial`（**空断言**） | ACCEPTED |
| L5 | 自由文本写 "Corollary 3.12 established"，`status` 仍 `RESEARCH_ONLY` | ACCEPTED |
| L6 | `axioms_log` 指向 3 字节 stdout（**公理从未记录**） | ACCEPTED |
| L7 | `run.cwd` 指向**整个仓库根**而非隔离交付目录 | ACCEPTED |
| L8 | 干脆不给 declarations、不给源码 | ACCEPTED |

**L3 最值得警惕**：预检器只校验"文件被登记且哈希自洽"，**不校验该日志是否属于本任务、其 `cwd`/`argv` 是否指向本任务目录**。跨任务搬运真实证据（最容易取信的那种）零成本通过。L1/L2 说明 PROTOCOL「最小交付」第 1、4 项**没有对应门禁**——文件名是什么都行。

---

## 6. 门禁守住了什么、漏了什么

**守住（HELD，21 例）**：SHA 自洽（真篡改）、路径逃逸（含 junction）、JSON 重复键、`exit_code` 类型、`status` 白名单精确匹配、`CLI_CANDIDATE` 必须有声明+Lean run+严格 flag+依赖回执+非零退出拦截、负数 duration、空 argv。

**漏掉（BYPASSED，22 例）**，按严重度：

1. **`sorry` / `sorryAx` / 公理白名单完全不检查** —— 已用 T049 真实证据实测放行（§0、§1(f)）。PROTOCOL 明令禁止的项，门禁零实现。
2. **`exit_code` 自报、日志内容零解析** —— 失败构建可盖章通过（§1(c)、§2.1）。此项使其余门禁全部失效。
3. **`RESEARCH_ONLY` 下 `runs` 可整段删除** —— 与「最小交付」第 3 项直接冲突。
4. **空构建无检测** —— `lake build` 无参、`lean -DwarningAsError` 无目标串，两例放行。
5. **自由文本可承载结论**（"VERIFIED"、"Cor 3.12 established"）。
6. **无时间维度** —— 源码晚于日志、日志被覆盖、跨任务搬运日志，均不可见。
7. **文件名/职责不校验** —— `replay_file`/`summary_file`/`axioms_log` 可指向任意已登记文件。

---

## 7. 需要父线程裁断 / 交付方回应

1. **T049 的 `sorryAx`**（§0）：`src\T049\FinitePlaceNorm.lean` 有 3 处 `declaration uses sorry`，6 个以上声明依赖 `sorryAx`。该任务定位是 `LEAN_CANDIDATE`，**如何处置？**
2. **`delivery.json` 一份都没有**（8/8）：是"尚未收尾"还是"不打算交"？否则 §1 的对抗结论只能代表"若将来提交"。
3. **T021 的失败证据已被覆盖**（§2.1、§4.3）：三次覆盖后只剩最后一次 `✖ Boundary.Frontier`。请确认交付方是否保留了完整构建历史，否则**失败记录不可回溯**。
4. **Reviewer A 的时间戳与目录清单与其自身写入时刻矛盾**（§4.4）——是否采信 A 的 ROLLUP，需父线程定。
5. **T015 `replay.ps1` 依赖 `pwsh`（本机不存在）**，仅 5.1 可用；建议交付方在脚本头把可用解释器写成硬前提，而不是注释。

---

## 8. 交付方做对的地方（红队也应记账）

- **T008 是本轮材料层最硬的一份**：第一份真实 `delivery.json`（13:33:57），我独立重算其 **14/14 产物哈希全中、0 失配**；`runs` 里三条（probe / replay / **discarded_attempt**）都带真实 argv、cwd、exit_code、duration、stdout/stderr；连**失败的那次尝试**（`exit_code: 1`）也如实登记，并在 `argv` 里明写 `<attempt-1 T008Probe.lean, since replaced>`。
- **T008 的 `SUMMARY.md` 质量高**：主动写明"**是否推进首个缺箭头：否**"、5 条未解决项、明确"不宣称 IUT 核心争议/Cor 3.12/abc"，并把 `Boundary/DecompositionBridge.lean` 无 `.olean` 不可核验一事**自己记为假设而非已构造**。这正是 PROTOCOL 想要的自限。
- **T008 的探针面对失败是丢弃而非修补**（源码注释："would have been a fabricated arrow, so it was discarded, not repaired"）。
- **T015 是唯一完全可回放、只读、时间序自洽的交付**，`replay.ps1` 自述限制清晰、`-SkipNetwork` 可离线，重放复现 PASS 且不污染（38/39 文件字节不变）。
- **T021 的 trace 行目标显式**（`.../Boundary/Frontier.lean`），符合 PROTOCOL「显式列出本任务文件或模块」；且带 `-DwarningAsError=true`。
- **T008 探针日志公理全在允许清单内**（11 条逐条核对为 `propext / Classical.choice / Quot.sound`，0 error / 0 warning / 0 sorry）。

**红队结论：门禁的材料层（SHA/路径/白名单/候选约束）是硬的——T008 的 14/14 哈希就是它守住的；数学层（sorry、公理、退出码真实性、时间序）基本没有实现，而这正是本轮唯一被违反的那一层。**

> 反讽的一点，也是本报告最该被记住的一句：**T008 是唯一如实披露失败、材料层零失配的交付，而它（以及把它的诚实改掉之后的它）拿到的评语与伪造件完全相同——`PACKAGE_COMPLETE`。门禁目前无法区分诚实与隐瞒。**

---

## 9. 环境与边界（影响结论效力）

- 取证窗口 **13:09 → 13:32**，期间 **T008/T021/T049/T097 持续写入**（实测 T021 到 13:31:56、T008 到 13:31:31、T049 到 13:30:12 仍在变）。**§2.1、§4.3 所述的失败记录在写作过程中被覆盖/新增**；对"内容"的一切陈述只对抓取那一刻有效，不构成终局结论。
- 现场存在**正在运行的** `lake build Boundary.ThetaGermTransport` 与 `lake build T049`，另有 3 个 `lake serve`、4 个 `lean.exe`（`Get-CimInstance Win32_Process` 实测）。这解释了 T021 日志为何反复变化，以及 `Get-FileHash` 一度报 "being used by another process"。
- **T049 的隔离性存疑（13:27 版日志）**：曾出现 `plausible / LeanSearchClient / importGraph / proofwidgets / aesop / Qq / batteries / Cli` **8 个 GitHub clone**（`cloning https://github.com/...`），与 PROTOCOL「无自动下载」及任务卡"离线可运行"口径不一致。**注意：该内容在 13:30:12 版日志中已被失败输出覆盖，现不可复现**，故仅作提示、不作判定。
- 我**没有**运行 T021/T049 的 Lean 重建（会与当时正在运行的进程争用 `.lake`，且属写操作），故那几条按 `NOT_REPLAYABLE` / 未重放记，**不是"重放失败"**。
- **T008 的 Lean 重放（§C.4）确实执行了**：按声明原样 argv + cwd，耗时 49.42s，exit 0。执行前后 `candidates/core-kummer` 34 个源文件 SHA256 全部不变、`.lake` 最新文件仍为 `11:58:20`，**证明只读**。
- 仓库内零破坏性写入：坏输入全在 `%TEMP%\c-redteam\`；触碰仓库的只有 §3 的 T015 重放（脚本设计为自写 `logs/`，我前后逐文件 SHA256 比对证明 38/39 字节不变，备份在 `%TEMP%\c-redteam\T015-logs-backup`）与 §C.4 的 T008 Lean 只读重放。
- 截止 **13:39**，`delivery.json` 仍只有 **T008 一份**（17003B，13:36:40）；其余 7 个目录无。T021 的 `logs/build-snapshot-ThetaGermTransport.log` 在 13:21→13:32 间被覆盖 **3 次**，每次都是失败的构建尝试，旧内容不可回溯。
- 本机无 `pwsh`，`python` 为 3.14.5。

---

### 附：46 例判定一览（逐例取自 `redteam-results.json` / `redteam-round2.json`）

**第一轮 38 例** → 检查器 `REJECTED 21` / `ACCEPTED 17`：

| 计数 | 用例 |
|---|---|
| `ACCEPTED` 17 | SANITY×1（阳性对照，应过）、(a+) 哈希同步刷新、(b) 删 `runs`、(c) 日志含错却报 0、(c+) 同上、(d) symlink（**作废**）、(f)×4、(2a)(2b)(3)、t(✖/error)、t(自由文本 VERIFIED)、t(`cwd` 指仓库外)、(4) mtime |
| `REJECTED` 21 | (a) 纯篡改、(b+) `runs=[]`+candidate、(b) 删 stdout、(c) 字符串 "0"、(c) JSON true、(d) 逃逸×3、(e) 白名单×7、(2c) 裸 lake build、(t) candidate 但 exit=1、(t) 负 duration、(t) 空 argv、重复 JSON 键 |

**第二轮 8 例** → `BYPASSED 8`（L1–L8）。

**净计**：
- **`HELD` = 21**
- **`BYPASSED` = 14 + 8 = 22**（17 个 ACCEPTED 中扣掉 SANITY 对照与作废的 symlink）
- **`NOT_APPLICABLE` = 1**（symlink，`WinError 1314` 从未执行）
- 另 **1 例属"门禁过严"误报**（`sub/../../SUMMARY.md` 解析后仍在根内却被拒），对交付方偏严，不计入 BYPASSED。
- §0/§1(f) 的 **T049 真实证据实验**为额外 1 例，已在正文单列，未计入上表。

---

# 第二部分：以 **真实 T008 交付** 为靶子（按父线程指令追加，13:39）

> 本节全部用例都是对 `delegated/2026-10-24/T008/delivery.json`（17003B，13:36:40）的**字节级副本**做最小改动，仓库内真实文件**未改动一个字节**。
> 脚本：`%TEMP%\c-redteam\redteam3.py`；结果：`redteam-round3.json`（16 例）。

**基线（副本未改动）**：

```
[BASELINE ] unmodified real T008 delivery    exit=0 PACKAGE_COMPLETE
```

## C.1 六类坏输入（第 1 项）

```
[BASELINE] unmodified real T008 delivery                     exit=0 PACKAGE_COMPLETE
[HELD    ] (a) 1 byte appended, SHA not updated              exit=2  artifact SHA mismatch: logs/probe.stdout.log
[BYPASSED] (b) delete runs[] (commands_run)                  exit=0
[BYPASSED] (c) discarded-attempt exit 1 -> 0                 exit=0
[BYPASSED] (c+) scrub log + exit 1 -> 0                      exit=0
[HELD    ] (d) summary_file = ../../../etc/passwd            exit=2  path escapes delivery
[HELD    ] (d) artifacts[0].path escapes root                exit=2  path escapes delivery
[HELD    ] (e) status = VERIFIED                             exit=2  invalid status
[HELD    ] (e) status = PASS                                 exit=2  invalid status
[HELD    ] (f) inject 'sorry' + status CLI_CANDIDATE         exit=2  run input SHA mismatch
[BYPASSED] (f+) add sorryAx to the axioms log                exit=0
```

与前两轮（自建 fixture）**结论一致**，且在真实文件上复现：

- **(a)(d)(e) HELD** —— 篡改、逃逸、白名单三道门在真实文件上同样有效。
- **(b) BYPASSED** —— 直接 `del runs`，**`PACKAGE_COMPLETE` 照发**。
- **(c)(c+) BYPASSED** —— 把 T008 唯一那条**如实登记的失败**（`discarded_attempt`，`exit_code: 1`）改成 `0`；连日志一起洗白也照样通过。**这是本轮最刺眼的一条**：门禁对"诚实披露失败"与"隐瞒失败"给出**完全相同**的评语。
- **(f) HELD 但属偶然** —— 因为我给探针追加了 `sorry` 却只刷新了 `probe/T008Probe.lean` 的哈希，**没刷 `runs[0].inputs[]` 的哈希**，于是被 `run input SHA mismatch`（line 140）拦下。**拦住它的是哈希绑定，不是"sorry 检查"**——只要同步刷新三处哈希就通过（见 §C.3 与 §1(f) 已证）。
- **(f+) BYPASSED** —— 直接在 `axioms_log` 里写入 `[propext, sorryAx, Classical.choice, Quot.sound]` 并刷新哈希，**exit=0**。PROTOCOL 明确禁止 `sorryAx`，门禁不看内容。

## C.2 "18 条已构造箭头"的强度错标（第 2 项 —— 父线程重点）

T008 的真实声明结构：

```
arrow_counts = { total: 23, constructed: 18, hypothesis: 5,
                 constructed_with_extra_hypotheses: 6,
                 constructed_ids: [A01..A18], hypothesis_ids: [A19..A23],
                 constructed_with_extra_hypotheses_ids: [A06,A13,A14,A15,A16,A17] }
scope_statement = "Type ledger only. No new mathematics, no new Lean declaration, no axiom, no sorry.
                   23 arrows: 18 constructed ...; A PASS in this package is NOT a fact-tree admission ..."
```

实测：把这份**保守自限的声明**改成**冒进的强断言**，预检器**毫无反应**：

```
[BYPASSED] (2)  18 -> 23 constructed, hypothesis=0, not_claimed=[],
                scope_statement="All 23 arrows CONSTRUCTED and unconditional ...
                                 closes the IUT core gap."          exit=0
[BYPASSED] (2+) erase constructed_with_extra_hypotheses (6 -> 0),
                scope_statement="18 arrows constructed, none conditional."   exit=0
[HELD    ] (2+) status RESEARCH_ONLY -> CLI_CANDIDATE
                   exit=2  candidate records a nonzero exit
```

**结论（父线程预期被证实）**：预检器**没有任何机制**能发现"标错强度"。

- `arrow_counts`、`scope_statement`、`not_claimed` 这些字段**根本不在 `delivery_check()` 的读取范围内**（对照 `check_delivery.py:92-178`：只读 `schema_version/task_id/task_card_sha256/baseline_sha256/status/artifacts/summary_file/replay_file/gap_file/runs/declarations/dependency_deliveries/editor`）。它们是**自由 JSON**，写什么都不会被看。
- 唯一"沾边"的一条是 `CLI_CANDIDATE` 要求所有 run `exit_code == 0`（line 143-144）。T008 诚实保留了 `discarded_attempt` 的 `exit: 1`，所以它**升不了级**——但这不是强度检查，只是"有没有如实记过失败"。换句话说：**一个撒谎把 `exit` 全写成 0 的交付，反而能升到 `CLI_CANDIDATE`；如实记录的 T008 升不上去。** 门禁的激励方向是反的。
- 即便交付方写成 `CLI_CANDIDATE`，门禁也只查"有没有声明 + 有没有带 `-DwarningAsError` 的 lean run + 依赖回执"，**不查任何一条箭头是真的**。

## C.3 provenance 洗白（顺带测，最隐蔽）

```
[BYPASSED] (p) 4 条 declarations 的 source_file 全部改指 SUMMARY.md，
              source_sha256 同步刷新                              exit=0
[BYPASSED] (p) axioms_log 全部改指空的 logs/replay.stderr.log     exit=0
```

T008 的 4 条声明 `source_file` 都指向 `probe/T008Probe.lean`（一个**只做 `#check`、不定义任何东西**的文件——它自己在开头写明 "This file defines nothing"），而真身 `KummerTheory.Decomposition.*` 在 `candidates/core-kummer/.../Decomposition.lean`。
预检器只要求 `source_file` 是"已登记且哈希一致的文件"（line 151-152），**不要求该文件真的包含这个声明**。我把它改指 `SUMMARY.md` —— 同样 exit 0。
→ 这不影响 T008（它已用 `upstream_inputs` 诚实登记了真身哈希），但说明**该字段对伪造完全不设防**。

## C.4 T008 的 replay 实测（第 3 项）

**声明的 run[0]**：

```
argv = ['lake','env','lean','-DwarningAsError=true',
        'D:\...\delegated\2026-10-24\T008\probe\T008Probe.lean']
cwd  = D:\Inter-universal Teichmüller Theory\candidates\core-kummer
exit_code = 0, duration_seconds = 49.06
```

**前置条件**：`candidates/core-kummer/lake-manifest.json` 存在，`.lake/build/lib/lean` 有 26 个 `.olean`（含 `Kummer/Decomposition.olean`），无进程占用。

**实跑**（原样 argv、原样 cwd）：

```
$ cd "D:\...\candidates\core-kummer"
$ lake env lean -DwarningAsError=true "D:\...\T008\probe\T008Probe.lean"
[REPLAY exit=0  elapsed=49.42s  declared exit=0 dur=49.06s]
replayed output lines: 203
```

**与它存的日志逐字比对**（`logs/probe.stdout.log` 是 UTF-16LE，需先解码）：

```
stored text len: 14672   replay text len: 14671
diff lines: 5   -> @@ -1 +1 @@   仅首行差一个 BOM 残留 (@Subgroup.subtype …)
axioms lines stored: 11   axioms lines replay: 11
error lines in replay: 0
```

**判定：REPLAYABLE / PASS。** exit code 一致（0=0）、耗时一致（49.42s vs 声明 49.06s）、**11 条 `#print axioms` 全部复现、0 error**，唯一差异是首行 BOM——属日志编码伪影，非内容差异。

**只读性验证**：重放后 `candidates/core-kummer` 的 34 个源文件 SHA256 **全部不变**，`.lake` 内最新文件仍是 `11:58:20`（重放未写任何 olean）。**`lake env lean` 未污染项目缓存。**

> 这一条对交付方是**加分项**：T008 的 Lean 证据是**真跑得出来、且与所存日志一致**的。它与 §C.2 的问题互不抵消——**证据真实，但门禁无法判断这份证据支撑的 18 条箭头强度是否被正确标注**。

## C.5 预检器能覆盖 / 不能覆盖什么（父线程第 2 项的正面回答）

| 能覆盖（实测有效） | 依据 |
|---|---|
| 交付物字节与登记 SHA 一致 | line 112；T008 14/14 实算全中 |
| 产物/日志文件存在且被登记 | line 107, 116-119 |
| 路径不逃逸交付根（含 junction/绝对路径） | line 44-47 |
| `status` 属四值白名单、精确匹配 | line 16, 102 |
| 任务卡/baseline SHA 与目录对得上 | line 99-100 |
| `exit_code` 是 int、`duration` 是有限非负数、`argv` 非空 | line 129-135 |
| `CLI_CANDIDATE`/`EDITOR_CANDIDATE` 要求：全部 run `exit==0`、有声明、有带 `-DwarningAsError=true` 的 lean run、依赖回执齐全、声明绑定到某次 lean run 的输入 | line 143-144, 155-161, 168-170 |
| JSON 重复键 | line 23-29 |
| 目录内产物路径大小写去重 | line 109 |

| 不能覆盖（实测绕过） | 后果 |
|---|---|
| **日志内容**（`error:`/`✖`/`sorry`/`sorryAx`） | 失败构建、带 sorry 的构建一律放行 |
| **`exit_code` 的真实性** | 全是自报；谎报 0 即通过 |
| **声明/断言的强度**（`arrow_counts`/`scope_statement`/`type` 语义） | 18→23、取消全部额外前提，无感 |
| **`source_file` 是否真的包含该声明** | 改指 `SUMMARY.md` 亦通过 |
| **`axioms_log` 内容是否在白名单内** | 写 `sorryAx` 亦通过 |
| **时间序**（源码/日志 mtime、日志被覆盖） | 无时间维度 |
| **跨任务证据搬运** | 别的任务的真实日志可当本任务证据 |
| **文件名/职责**（`summary_file`/`replay_file` 是否名副其实） | 指向任意已登记文件 |
| **自由文本字段** | `research_result`、`scope_statement` 可写任何结论 |

**一句话**：`check_delivery.py` 是一台**材料完整性校验器**（"文件在不在、对不对得上号"），**不是**一台**证据真实性/结论强度校验器**。它的 docstring 与 `scope` 字段其实说得很诚实（"Material and hashes only… mathematics, axioms, source semantics … remain unverified"）——**问题在于流程上 `PACKAGE_COMPLETE` 极易被读成"通过验收"**。

## C.6 第二部分判定汇总

`round3` 共 16 例：`BYPASSED 8` / `HELD 7` / 基线通过 1。

- BYPASSED：`del runs`、失败 exit 1→0、洗日志+改 exit、`sorryAx` 入 axioms log、18→23 强断言、抹掉"带前提"集合、声明改绑 `SUMMARY.md`、`axioms_log` 改指空日志。
- HELD：1 字节篡改、路径逃逸 ×2、`status=VERIFIED`、`status=PASS`、注入 sorry 但漏刷 inputs 哈希（**偶然拦住**）、`RESEARCH_ONLY`→`CLI_CANDIDATE`（因存有 exit=1 记录）。

**累计（第一 + 二部分）**：`BYPASSED 30` / `HELD 28` / `NOT_APPLICABLE 1`。

---

# 第三部分：四份**真实**交付的复查 + 真破坏（按父线程第二轮指令，14:11）

> 对象：`T003`、`T008`、`T066`、`T097` 四份**真实** `delivery.json`。
> 破坏只在 `%TEMP%\c-redteam\l7\`、`l8\` 的副本上做，**仓库原件一个字节未改**。
> 脚本：`redteam4.py`（审计）、`redteam5.py` / `redteam5_t003.py`（破坏）；结果 `redteam-round5.json`。

## D.1 四份交付的逐项审计（回答父线程四个问题）

```
T003  9209B  status=RESEARCH_ONLY  artifacts=21  runs=4  declarations=0   -> PACKAGE_COMPLETE
T008 17003B  status=RESEARCH_ONLY  artifacts=12  runs=3  declarations=4   -> PACKAGE_COMPLETE
T066  8975B  status=RESEARCH_ONLY  artifacts= 7  runs=2  declarations=0   -> PACKAGE_COMPLETE
T097  7167B  status=RESEARCH_ONLY  artifacts=11  runs=1  declarations=0   -> PACKAGE_COMPLETE
```

| 父线程问的问题 | 实测结果 |
|---|---|
| **① 有别的任务把 `delivery.json` / 自产出 manifest 自引用进哈希表？** | **没有。** 四份 `artifacts` 均不含自身。我另做**间接**自引用扫描（在每个 artifact 内文搜 `delivery.json` 的 sha256 与自身 sha256）：**0 命中**。4 处命中全是**良性引用**——T003 `SUMMARY.md` L98 明写"`delivery.json` 自身不在 `artifacts` 内（清单不能包含自己的 SHA256）；其当前 SHA256 记在 `.tmp/…`"；T097 `quantifiers.json` 仅把 `delivery.json` 列为交付物名。**父线程修掉后未再复现。** |
| **② 有 run 声称 exit 0 但日志实为空构建/空输出？** | **没有空构建。** 全部日志 **0 处**出现 `no targets specified` / `Nothing to build`。详见 D.2。 |
| **③ 有 artifact 路径逃逸或指向 `delegated/` 之外？** | **没有。** 四份共 51 个 artifact，解析后全部落在各自任务目录内。 |
| **④ 有 `status` 写成白名单外？** | **没有。** 四份全为 `RESEARCH_ONLY`。 |

### D.2 逐 run 日志内容核查

| 任务 | run | exit | 日志实况 | 判定 |
|---|---|---|---|---|
| T003 | 4 条 `source_retrieval` | 全 0 | `OK .tmp/decls_dump.txt`(24B)、`OK .tmp/sigs.txt`(18B)、`entries=106 gaps=5 files=7`(245B)、`result=ALL_GAPS_CONFIRMED failures=none`(41B) | 内容真实非空；**非编译证据**（任务自己声明"未构建、未 `lake env lean`"，属诚实自限） |
| T066 | 2 条 `source_pin_check` | 全 0 | 两次各 9972B，**逐字节相同**（`T066 REPLAY: source pin verification (read-only)` + `PASS <sha> handoffs/a…`） | 真跑、可复现，且**主动做了两次确定性复跑** |
| T097 | 1 条 `audit` | 0 | `{"verdict":"ALL_ANCHORS_VERIFIED","checks_run":197,"checks_failed":0,"failures":[]}` | 内容真实；"failed"来自 `checks_failed:0` 字段名，**非错误** |
| T008 | 3 条 | 0 / 0 / **1** | run2 日志含 `HAS_ERROR,HAS_SORRY` | **唯一非零日志，且是交付方自己如实登记的失败**（见 §C.1） |

**需注意（非缺陷，但门禁看不见）**：T066/T097 的 `runs` 只是**脚本自检**（pin 校验／转写审计），**没有任何 Lean 编译动作**。二者都正确自限于 `RESEARCH_ONLY`，未越界宣称——若将来写成 `CLI_CANDIDATE`，门禁会要求"有带 `-DwarningAsError=true` 的 lean run"，它们没有，**那道门拦得住**。

## D.3 真破坏测试（父线程指定：改一字节 / 改 exit_code）

每份都**先确认副本本身可通过**，再破坏：

```
T003  [baseline ] unmodified copy                     exit=0 PACKAGE_COMPLETE
      [HELD     ] +1 byte on SUMMARY.md               exit=2  artifact SHA mismatch: SUMMARY.md
      [HELD     ] +1 byte on run[0].stdout            exit=2  artifact SHA mismatch: logs/extract.stdout.log
      [BYPASSED ] set 0 nonzero exit_code -> 0        exit=0
      [BYPASSED ] run[0].exit_code 0 -> 1             exit=0
      [BYPASSED ] delete all 4 runs (commands_run)    exit=0
      [HELD     ] summary_file -> ../../../../Windows/win.ini  exit=2  path escapes delivery
      [HELD     ] status -> VERIFIED                  exit=2  invalid status
      [HELD     ] status -> PASS                      exit=2  invalid status
      [HELD     ] self-reference: add delivery.json to artifacts  exit=2  artifact SHA mismatch: delivery.json
```

**T008 / T066 / T097 三份结果完全同型**（各 9 例，`HELD 6 / BYPASSED 3`），`BYPASSED` 的永远是这同一组：

```
[BYPASSED ] set <n> nonzero exit_code -> 0        (T008 n=1；T066/T097 本无失败可隐瞒，仍通过)
[BYPASSED ] run[0].exit_code 0 -> 1 (recorded failure)
[BYPASSED ] delete all <n> runs (commands_run)
```

**结论（父线程问题的正面回答）**：

1. **"改一个字节"——预检器真的拒绝。** 四份 × 2 类目标（普通 artifact + run 引用的日志），**8/8 全部 `HELD`**，错误信息精确到文件（`artifact SHA mismatch: logs/extract.stdout.log`）。**这道门很硬，可以为它签字。**
2. **"改 exit_code"——预检器完全不拒。** 两个方向都过：把失败改成 0（隐瞒）**和**把成功改成 1（伪造失败）**都返回 `PACKAGE_COMPLETE`**。四份 × 2 方向 = **8/8 BYPASSED**。
3. **"删掉整段 runs"——完全不拒。** 四份 **4/4 BYPASSED**。`RESEARCH_ONLY` 下 `runs` 是**可选字段**（`data.get("runs", [])`，line 125）。
4. **"重新引入 T003 自引用"——正确拒绝**（`artifact SHA mismatch: delivery.json`）。说明那个坑**门禁本能拦**，T003 当初只是没在交付前跑预检。
5. **路径逃逸 / status 白名单——四份 8/8 全拦。**

## D.4 第三部分发现的**新**问题

### 新问题 1：T003 的 `delivery.json` 是生成器脚本产物，期间出现过"陈旧包"

T003 目录有 `.tmp/make_delivery.py`（14:10:48）、`.tmp/run_records.py`（14:10:00）。14:09 我第一次跑四份审计时，T003 **恰好**因 `replay.ps1`（14:10:27 重写）与 `delivery.json`（14:09:25 生成）不同步而失败：

```
14:09:25  delivery.json 生成
14:10:27  replay.ps1 被重写（未同步刷新 delivery.json）
          checker -> PACKAGE_INCOMPLETE: artifact SHA mismatch: replay.ps1
14:11:18  delivery.json 重新生成 -> PACKAGE_COMPLETE
```

**不是 T003 的错，而是流程警告**：只要存在"先生成 `delivery.json`、后又改产物"的时序，包就会静默变陈旧。**预检器是唯一能发现这件事的工具，这次它确实发现了。**

**这个现象在我写报告期间复发了第二次**（14:13:18 复查）：

```
14:11:18  重新生成 -> PACKAGE_COMPLETE
14:13:18  再查     -> PACKAGE_INCOMPLETE: artifact SHA mismatch: replay.ps1   (又被重写)
```

即**同一个"生成器写清单 → 之后又改产物"的回路在 2 分钟内触发两次**。**建议：把 `check_delivery.py` 定为收尾的强制最后一条命令（且必须是"最后一次修改产物之后"），并发给生成型流程一条硬规则——产物落盘完成前不得先写 `delivery.json`。**

### 新问题 2：自产出 manifest 的**间接**自引用尚无实例，但协议没堵

四份都没有把自产 manifest 列进 `artifacts` 形成环；T003 把 `.tmp/runs.json`、`.tmp/gapcheck.json` 等列进 artifacts 属合法（不由 `delivery.json` 派生）。**风险在 `make_delivery.py` 这类生成器**：一旦形成"生成器 → 清单 → 生成器读清单"回路，会出现比 T003 那次更难查的自引用（不直接列自己，而是列一个**内容包含** `delivery.json` 哈希的文件）。**本轮无实例，仅作原理提示。**

### 新问题 3（**影响父线程结论**）：`764c7b3` 这个"构建图修复"**不在 HEAD 上**

父线程 pitfalls 文档称"提交 `764c7b3` 补全 roots，`lake build Boundary` 从零构建 exit 0（8789 jobs / 504.2 s），`DecompositionBridge.olean` 首次生成"。实测：

```
$ git merge-base --is-ancestor 764c7b3 HEAD        -> exit=1   (NOT an ancestor)
$ git branch -a --contains 764c7b3                 -> + fix/portable-mathlib
$ git show HEAD:candidates/core-kummer/lakefile.lean        -> 1 line  (!)
$ git show 764c7b3:candidates/core-kummer/lakefile.lean     -> 69 lines
$ git status --porcelain -- candidates/core-kummer/lakefile.lean -> ?? (untracked)
$ HEAD = aa4a320
```

即：**当前在用的 `candidates/core-kummer/lakefile.lean`（694B，只声明 `ContinuousKummerTheory` 4 roots + `ValuationSupport` + `CoreKummer` 2 roots）在 HEAD 里根本不存在**；`764c7b3` 挂在 `fix/portable-mathlib` 旁支。而那个 `DecompositionBridge.olean` **只存在于 `.wt/portable/…` 这个可移植工作树里**，不在 `candidates/core-kummer/.lake`。

**实测当前缺口**（32 模块 vs 26 olean）：

```
lean modules: 32    oleans: 26
NO OLEAN (7):  Boundary/DecompositionBridge, Boundary/LaurentPoint,
               ExportAnchoredComparison, ExportFrontier,
               ExportProjectiveComparison, ExportThetaGermTransport, lakefile
```

→ **父线程缺陷 3 的"处置"结论目前不成立**：修复未进主线，olean 也只在游离 worktree。**T008 的 A21 仍无法在主工作区核验，其"记为假设"的处理依然正确且必要。** 建议确认 `fix/portable-mathlib` 是否该合入 `HEAD`，否则后续所有依赖 `Boundary.*` 的核验都会踩同一坑。

### 新问题 4（我自己的更正）：T008 `scope_statement` 的"强断言"是**误报**

我的自动扫描一度把 T008 `scope_statement` 标为 `STATUS_SMUGGLE`。复核原文：

> "Type ledger only. No new mathematics, no new Lean declaration, no axiom, no sorry. 23 arrows: 18 constructed …, 5 still hypotheses. **A PASS in this package is NOT a fact-tree admission and does not address the IUT core dispute, Corollary 3.12 or abc.**"

**这是带完整否定的自限陈述，不是抬高。撤回该条指控。** 记此以免父线程误读——也说明"自由文本扫描"本身会误报，这正是不能让门禁去猜语义的理由。

## D.5 第三部分判定汇总

`round5` 共 **45 例**（四份各 9 例，T003 因测期间被改写而整套重跑）：

- **`HELD` 33**：改一字节 ×8、路径逃逸 ×4、status 白名单 ×8、自引用重引入 ×4，及 T003 首次跑的连带拦截。
- **`BYPASSED` 12**：`exit_code` 双向篡改 ×8、删除 `runs` ×4。**四份交付全部命中，无一例外。**

**累计（一 + 二 + 三部分）**：`BYPASSED 42` / `HELD 61` / `NOT_APPLICABLE 1`。
