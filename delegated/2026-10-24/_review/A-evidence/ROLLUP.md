# A-evidence ROLLUP — 2026-10-24 交付审查（Reviewer A：证据与门禁）

- 审查范围：`delegated/2026-10-24/<Txxx>/`
- 审查轮次：第 1 轮 + 第 2 轮（第 2 轮详见 `round2.md`）
- 审查时刻（UTC）：2026-10-24 ~04:1x（第 1 轮）／~05:2x（第 2 轮）
- 审查方式：只读、对抗性、一律自行重算，不采信交付方自检

> **第 2 轮结论已追加在本文件末尾（§R2）与 `round2.md`。** 第 1 轮部分保留原文不改，以便对照。

---

## 目录存在性（本轮实测）

`Get-ChildItem delegated/2026-10-24 -Directory` 仅返回 **`T002`** 一个目录。

| 任务 | 目录 | 本轮处理 |
|---|---|---|
| T001 | 不存在 | NOT_YET |
| **T002** | 存在（仅 `.tmp/`） | **UNDECIDABLE**（已出 T002.md） |
| T003 | 不存在 | NOT_YET |
| T005 | 不存在 | NOT_YET |
| T008 | 不存在 | NOT_YET |
| T015 | 不存在 | NOT_YET |
| T065 | 不存在 | NOT_YET |
| T066 | 不存在 | NOT_YET |
| T097 | 不存在 | NOT_YET |
| T021 | 不存在 | NOT_YET |
| T049 | 不存在 | NOT_YET |

---

## 判定表

| 任务 | 判定 | 最硬的一条问题 |
|---|---|---|
| T001 | NOT_YET | 目录未出现 |
| **T002** | **UNDECIDABLE** | **5 份 0 字节日志 + `lean-build.log` 仅 20 行纯 axioms，退出码无完整 stdout/stderr 支撑；且 `delivery.json` 未落盘。第 4 条门禁（`#print axioms`/sorry/axiom）PASS，114/114 输入哈希实算全中。** |
| T003 | NOT_YET | 目录未出现 |
| T005 | NOT_YET | 目录未出现 |
| T008 | NOT_YET | 目录未出现 |
| T015 | NOT_YET | 目录未出现 |
| T065 | NOT_YET | 目录未出现 |
| T066 | NOT_YET | 目录未出现 |
| T097 | NOT_YET | 目录未出现 |
| T021 | NOT_YET | 目录未出现 |
| T049 | NOT_YET | 目录未出现 |

判定分布：`PASS 0` / `FAIL 0` / `UNDECIDABLE 1` / `NOT_YET 10`

---

## T002 六条门禁速览

| 门禁 | 判定 | 依据 |
|---|---|---|
| 1 delivery.json SHA | UNDECIDABLE | 无 `delivery.json`；但 `.tmp/nodes.json` 的 `input_sha256` **114/114 全部实算一致**，父/祖先三份分片哈希亦一致 |
| 2 argv 显式目标 | UNDECIDABLE | 旁证 `lake env lean -DwarningAsError=true -o … Boundary/ThetaGermTransport.lean` 与 4 个 port 显式模块名；`nothing to build`/`no targets specified` **零命中**；olean 真实新鲜（源 11:57:48 → olean 11:58:20） |
| 3 退出码真实 / 日志完整 | **UNDECIDABLE ＋ 硬问题** | 5 份 0 字节日志（`export.stderr.log` + 4 个 port 日志）；`lean-build.log` 仅 20 行、纯 axioms；`exit_evidence` 为自述文字（"parent observed exec session 38398…"），不可回放 |
| 4 `#print axioms` / sorry / axiom | **PASS** | 源码 L237–254 共 18 条，与日志输出**逐行序全等**；无 `sorry`/`admit`/自加 `axiom`（4 处命中共为导出工具字符串字面量）；axioms 全在 `[Classical.choice, Quot.sound, propext]` 白名单内 |
| 5 状态标签抬高 | UNDECIDABLE | `status: VERIFIED_LOCAL_SHARD` 无标签字典可比对；`scope` 已明写 "no original IUT gap closure"（未见越界措辞）；`CLI_CANDIDATE`/`RESEARCH_ONLY` 均未出现 |
| 6 越界写入 | UNDECIDABLE | 5 个 fact-tree JSON 未列入 `input_sha256`（含同名 `core-germ-2026-10-24.json`）；`fact-tree/registry.json` 为 ` M` 但 mtime 10/21，**早于** T002，判为非本任务所写 |

---

## 对交付方的要求（复审前必须补齐）

1. 落盘 `delivery.json`，含每份产物的 sha256、字节数、行数。
2. Lean 命令以**结构化 argv 数组**给出（非拼接字符串），并标明目标模块/文件。
3. 退出码附**机器可读**回执（进程/job id + 实际 exit code），不得只写"parent observed …"。
4. 补齐 4 个 port 模块与 export 的 **stdout/stderr 全量**；0 字节日志须说明是"确实无输出"还是"未捕获"。
5. `lean-build.log` 需含编译过程行，不应只有 axioms 输出。
6. 给出 fact-tree 写入清单，声明 `core-germ-2026-10-24.json` 属产出还是输入。
7. 说明 `VERIFIED_LOCAL_SHARD` 的定义，或改用仓库内已有标签字典中的取值。

---

## 备注（本轮已排除的伪问题，避免下轮重复劳动）

- `get-content` 显示 `nodes.json` 的 `statement` 字段为 `鈭€ … K耍` 等乱码：**非交付缺陷**。原始字节按 UTF-8 解码为 `∀ {K : Type u_1} [inst : NormedField K] (a : Kˣ)`，正常；乱码系我早期控制台按 GBK 解码所致。`index_dump.txt` 同理。
- `nodes.json` 的 `selected_count: 18` 与 `graph_node_count: 25` **自洽**：25 节点 = 18 `selected:true` + 7 `selected:false`（后者全为 `._proof_*` 辅助项），非虚报。
- `Export*.lean` 中 `axiom` 命中为字符串字面量 `| .axiomInfo _ => "axiom"`，不构成自加公理。

---

# §R2 第 2 轮（13:25–13:29 本机）

完整过程见 `round2.md`。以下为判定与最硬问题。

## R2 判定表

| 任务 | R2 判定 | 最硬的一条问题 |
|---|---|---|
| T002 | UNDECIDABLE | 新增 `index_check.stdout.log` 自认 **"no Lean replay"**（只复算了自己存的哈希＝我已做过的事）；`research/core-germ-2026-10-24/` 的 **5 份 0 字节日志原封未动** |
| T003 | UNDECIDABLE | 纯源码静态提取（`targets.json` 是 mathlib 声明名映射），全目录 `lake|lean|exit=` **零命中**；无 delivery.json |
| T008 | UNDECIDABLE | `probe.stdout.log` 曾 32948 B → 被重写为 0 → 570 B（仍在反复跑），当前不足以支撑 ARROW-TABLE；**但 `RESEARCH_ONLY` 标注正确、无活跃 sorry（块注释内 2 处）** |
| T015 | **PASS** | 22 条命令全为 `rev-parse/cat-file/log/rev-list/diff/diff-tree/status`；无任何 checkout/reset/merge/fetch-write；`.git/FETCH_HEAD` mtime 仍为 01:46:01、`packed-refs` 02:32:52、`refs/heads/research/backward-paths` 仍 `d3c5599…` |
| T021 | UNDECIDABLE | **`logs/build-snapshot-ThetaGermTransport.log` 名实不符**：实际仅 3 行，构建的是 `ContH1.Corestriction / Kummer.Corestriction / Kummer.Values`，全文 **零次** 提及 ThetaGermTransport；`lakefile.toml` 的 defaultTargets 是 `["T021"]` |
| T049 | IN_FLIGHT | 30 s 内 `.lake/packages/` 仍在全量克隆（`tmp_pack_*` 反复出现/删除）；`logs/probe01.log` 0 B；`lakefile.lean` 硬编码 `C:/Users/18746/Desktop/数竞屠宰场/...` 非便携路径 |
| T065 | UNDECIDABLE | 静态 JSON 分析（`consumers 13/13`、`scaling 5/5`）但 `def_gen_producers_are_decls` 有 **2 条 `ok:false`**（`StripScaling.galInduced`、`StripScaling.shift_eq_zero`）未解释 |
| T097 | UNDECIDABLE | 行级引用（`L2060 page=44 markerL=2041`、Cor 3.12 `−|log(Θ)| ≥ −|log(q)|`）抽样对得上，但无 delivery.json、我未独立复算提取正确性 |

## R2 全局事实

1. **`delivery.json` 在 8 个目录中一个都没有**（`delivery*.json` 全树 `NONE FOUND`）。⇒ 主指令第 1 项在所有任务上**无对象**。
2. **无越界写入**：任务窗口内 `candidates/core-kummer/**` 与 `fact-tree/**` 均**零文件**改动。
3. 任务状态：T049/T021 仍在写；T008 仍在反复跑 probe；T015 于 13:27 被完整重跑一次（内容与 13:13 一致，非篡改）。

## R2 两个我自己推翻的怀疑（避免下轮重复）

- `git-difftree-reviewed-commit.stdout.log` 的 `M	research`（11 B，hex `4D 09 72 65 73 65 61 72 63 68 0A`）：是 `git diff-tree` **非递归**对目录的正确输出，非伪造；与 `1 file changed, 145 insertions(+)` 自洽。
- T008 probe 的 `sorry` 命中 2 处：**全在 L1–L20 的 `/- … -/` 块注释内**，无活跃证明义务。

---

# §R2-M 对 `independent-replay-core-germ.md` 的方法学复核

**结论：方向正确，但该记录的具体证据不可核验；其自评「UNDECIDABLE → PASS」我不能背书。**

## 可确认的部分（我已复算）
- 该记录对交付方缺陷的三项描述（5 份 0 字节日志、`lean-build.log` 仅 18 条 axioms、`port-build-exits.json` 无 argv/耗时）与我的实测**完全一致，属实**。
- 我实测 ThetaGermTransport 的**两个真实 import 均不陈旧**：`Boundary/ProjectiveComparison` src 11:24:44 → olean 11:26:07；`TateCurvesTheta/Kummer/ThetaGermCore` src 11:41:36 → olean 11:45:13。⇒ 若 replay 真按声明执行，**不易被旧 olean 欺骗**。

## 不可确认的部分（关键缺口）
- **该记录没有任何原始产物**：`_review/A-evidence/` 下仅有 3 个 `.md`，**没有 replay 的 stdout/stderr、没有 `--json` 原文、没有 job 回执**。
- 「`stdout bytes: 5835`」「58 information / 0 error / 0 warning」「elapsed 54.9 s」全部是**叙述性数字，无文件可复算**。按我判交付方 `UNDECIDABLE` 的同一把尺子，**叙述 ≠ 证据**，不能对主线放宽。
- 磁盘上**没有 replay 的指纹**：`ThetaGermTransport.olean` mtime 仍为 **11:58:20**（replay 声称约 12:1x）。这**不能证伪**（`lean <file>` 不带 `-o` 本就不写 olean），但也说明无从佐证那 54.9 s 真跑过。

## 三个技术点的评估
1. **`--json` 下 information vs error 可区分 —— 成立。** 每行一个 JSON 对象，`severity ∈ {information, warning, error}`；`#print axioms` 输出为 `information`，编译错误为 `error`。因此「0 error」在语义上确实能把「只是 axioms 摘要」与「真有报错」分开。但在 `-DwarningAsError=true` 下，必须看到 `severity:"error"` 计数为 0 才算证成——记录给了数，却没有原始文件。
2. **能否被旧 olean 欺骗 —— 部分能，且记录未设防。** `lean <file>` 只重新 elaborate 该文件，import 一律读现成 olean。故「源新、依赖旧」仍可 exit 0。正确设防应是**先核 import 的 mtime/哈希**，或对整包 `lake build <pkg>` 强制重编。本案风险**实际未发生**（两 import 均 fresh），但 `Boundary/LaurentPoint.lean` 在 `.lake` 下**无 olean**，说明该包确有「部分模块未建构」的相邻欠账。
3. **能否用旧 olean 整体冒名 —— 不能。** 源文件若有语法/类型错误必然报错，无法用旧 olean 顶替当前正文。故该 replay **能**证明「该 .lean 文本此刻可通过 elaborate」。

## 我的处置
把该记录的价值限定为「对交付方缺陷的**独立确认**」（此部分我已复算属实），**不采纳**其把主线升为 `PASS` 的自评。要升为 PASS，需补：`--json` 原始输出（或 job 回执）＋ argv 数组 ＋ 该次运行 exit code 机器回执 ＋ import 新鲜度核验。

---

# §R3 对 `independent-replay-core-germ.md` v2 的复核（含 v2 原始产物）

复核方式：**我自己重算**，不采信转述。

## R3-1 原始产物实测（全部一致）

| 项 | 声明 | 我的实测 | 结论 |
|---|---|---|---|
| `replay-run/stdout.jsonl` 字节 | 5817 | **5817** | ✅ |
| `replay-run/stdout.jsonl` sha256 | `7C302FBF…` | `7C302FBF7F7404FA83A3C8C575003113032CAE0CC5F833375B0D1D48555A2D4E` | ✅ 全等 |
| `replay-run/stderr.txt` | 0 B | **0 B**（sha `E3B0C442…` = 空文件标准哈希） | ✅ |
| severity 计数 | `{"information":18}`，error 0，warning 0 | 逐行 `ConvertFrom-Json`：**18 对象 / 0 不可解析 / `information=18`** | ✅ |
| 物理行数 | — | **18 行**，一行一对象，无折行 | ✅ |

**更强的一步（v2 自己没做，我补做）**：这 18 行不是"18 条随便什么 information"，而是与源码**行号级**咬合：

- 每行 `fileName` 唯一为 `Boundary/ThetaGermTransport.lean`；`kind = [anonymous]`、`isSilent=false`、`severity=information`。
- `pos.line` 序列 = `237,238,…,254`，**与源码 `#print axioms` 的 18 行 237–254 逐行全等**（order-sensitive `Compare-Object -SyncWindow 0` → IDENTICAL）。
- 提取的 18 个声明名与源码 L237–254 的 18 个 `#print axioms` **同名同序**。
- 公理名统计：`propext=18, Classical.choice=18, Quot.sound=18`——**无 sorryAx、无第四种公理**。

⇒ 这份 JSONL 是**真正的 elaborator 输出**，不是排版出来的摘要：伪造者若只拼 axioms 文本，极难同时把 `pos.line` 精确对到 237–254 且保持 `endPos/fileName/isSilent` 语义自洽。

## R3-2 v1「58 条」错误 —— 确认并正确归因

v2 §4 承认 v1 的 58 是错数字（把 PowerShell 输出行数含折行当成了记录数）。我实测**物理 18 行 / 18 对象**，v2 的 18 正确。
**这恰好验证了我第 2 轮拒绝背书 v1 的判断**：无原始产物 → 连自己写错数字都无法自查。v2 把这条因果写明白了，方向正确。

## R3-3 仍未设防（v2 已诚实标注，我确认其边界描述准确）

v2 只核了**两个直接 import** 的 mtime：
- `Boundary/ProjectiveComparison` src 11:24:44 → olean 11:26:07 ✅（我复核：一致）
- `TateCurvesTheta/Kummer/ThetaGermCore` src 11:41:36 → olean 11:45:13 ✅（我复核：一致）
**未递归传递 import** —— v2 自己写明了这点，我不另记缺陷，但记录该限界。
相邻风险仍在：`Boundary/LaurentPoint.lean` 在 `.lake` 下**无 olean**，说明该包存在"部分模块未建构"的欠账。

---

# §R3-ANSWER 三个问题的答复

## 问 1：原始产物是否足以支撑"该文件此刻可严格 elaborate"，以及是否仍不该升 PASS？

**分两层答，答案是"够支撑限定结论，但仍不该升 PASS"——而这已不再是对证据强度的否定，是结论范围本身。**

- **"该 .lean 文本在本机当前 import 集下以 `-DwarningAsError=true` 严格 elaborate 通过"** —— **证据充分，我认可。** 理由：JSONL 是逐行真输出、行号级咬合源码、0 error 0 warning、18 条 axioms 在白名单内、stderr 空文件、argv 显式点名文件（非 `lake build` 无参，故不存在 `nothing to build` 空转）。
- **但不该升 PASS，因为该命题的分母不覆盖三条声明**：
  1. **不覆盖 4 个 port 模块**。`tatecurves` 那 4 份日志仍是 0 字节、退出码仍无进程回执（v2 §5 自己也这么写）。主线重放**不能**替 port 模块背书。
  2. **不覆盖数学正确性**。编译通过 + 公理干净 ≠ 命题为真。`scope` 明写 "no original IUT gap closure"。
  3. **不覆盖"交付方原证据成立"**。这条重放是**主线另起一次运行**，它证明的是"文件能编译"，不是"交付方当时确实编译过"。交付方那 3 条 `parent observed exec session 38398/50991/30184` 仍是自述。

⇒ **我给出的准确结论**：主线 `ThetaGermTransport` 一条 = **PASS（限定条件：本机当前 import 集、该 SHA 的源文件、`#print axioms` 白名单内）**；**4 个 port 模块与交付方退出码链 = 维持 UNDECIDABLE**。二者不得合并成一条 PASS。

## 问 2：v2 的证据强度与判 T002 UNDECIDABLE 的尺子是否一致？

**一致了。** 我用的尺子只有三条，v2 现在三条都过：

| 尺子 | T002 | v2 | 判 |
|---|---|---|---|
| ① 原始产物落盘、可独立重算 | `lean-build.log` 仅 20 行 axioms，无过程行 | `stdout.jsonl` 5817 B 真输出，我逐行解析复算全中 | v2 过 |
| ② 退出码有真实进程回执 | 仅 `parent observed exec session …`（自述、不可回放） | 外层 shell `$LASTEXITCODE` + Stopwatch 54.4 s | v2 过 |
| ③ 命令显式目标、无空转假通过 | 显式（旁证），但日志不足以证明跑过 | argv 数组点名 `Boundary/ThetaGermTransport.lean` | v2 过 |
| ④ 不把"编译通过"写成"已证" | — | v2 §5 明写"不可以断言任何数学命题为真" | v2 过 |

**唯一残留的不对称（必须说清）**：T002 的 4 份 port 模块与 `export.stderr.log` 是 **0 字节**、退出码不可回放；v2 的对应物是 **5817 B 真输出 + 0 B stderr**。差别不在"0 字节"这个现象本身，而在**能否独立复算**——v2 能，T002 的 port 那 4 份不能。所以：
- **同一把尺子下，v2 达标、T002 的 port 部分不达标。这不是我前后不一，是对象不同。**

**我还是提一条小意见**：v2 的 `elapsed: 54.4 s` 仍只有叙述（Stopwatch），没有把计时值写进任何一个原始文件；`exit: 0` 也只有 md 里的文字，没落成 `exit.txt`。**若严格对齐"一切结论须有落盘物"**，建议补 `replay-run/exit.txt`（内容 `0`）与 `replay-run/timing.txt`（`54.4`）。这不改变我的判定，只是把最后两个纯叙述数字消掉。

## 问 3：`research/core-germ-2026-10-24/` 那 4 份 0 字节 port 日志按协议算什么状态？

**按协议 = `UNDECIDABLE`（证据缺失），不是 FAIL，也绝不能算 PASS。**

- `TateCurvesTheta-{QParameter-Basic, Theta-Basic, Theta-Periodicity, Kummer-ThetaGermCore}.log` 各 **0 B**（实测仍是 0 B，未被补充）。
- `port-build-exits.json` 给了 4 条 `exit_code: 0`，但**无 argv、无 stderr、无耗时、无进程号**——属自述值。
- 判定依据：0 字节日志**无法区分**「真的跑过且无输出」与「根本没跑」。按我的口径，无法区分即 `UNDECIDABLE`；而 `exit_code:0` 若被当作通过依据，就落进"空转/自述被记成通过"的靶心。
- **协议上应是**：`UNDECIDABLE`，且**阻塞**"4 个 port 模块已建构"这一声明；不得写入 fact-tree 的已验证集。
- **一条正向旁证（但不解门禁）**：T021 的快照工程在 13:21:40–13:31:46 独立产出了**同名 4 个模块的 olean**（`QParameter/Basic` 96632 B、`Theta/Basic` 262240 B、`Theta/Periodicity` 222552 B、`Kummer/ThetaGermCore` 493688 B）。这**提高了我对"这些模块确实可编译"的信心**，但它是**另一个工程、另一次运行**，不能替代交付方对那 4 份 0 字节日志的举证责任。⇒ 状态仍为 `UNDECIDABLE`。
