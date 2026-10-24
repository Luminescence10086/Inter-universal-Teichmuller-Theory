# A-evidence 第 2 轮：多任务复审

审查人：独立审查官 A（只读）。审查时刻：2026-10-24 13:25–13:29（本机）。
方法：目录静止性用 25s/30s 两次快照比对；一切哈希自行重算；不采信任何自述。

---

## 0. 全局事实（先于逐条判定）

1. **`delivery.json` 在全部 8 个目录中一个都没有。**
   `Get-ChildItem -Recurse -Filter "delivery*.json"` → `NONE FOUND`。
   ⇒ 主指令第 1 项（逐条重算 delivery.json 的 sha256）**无对象可审**，8 个任务均不可用该条门禁。

2. **静止性快照**（13:24:49 / 13:25:14 / 13:28→13:29 共三次）：
   - **T049 = IN_FLIGHT**：30s 内新增数百个文件（`.lake/packages/{aesop,Qq,proofwidgets,batteries}` 全量克隆中，含 `.git/objects/pack/tmp_pack_*` 与随后 `GONE` 的 tmp 包）。仍在拉依赖。
   - **T021 = IN_FLIGHT**：持续产出 `.olean/.ilean/.c/.setup.json`，13:29 前后仍在落 `Kummer/Corestriction.olean`。
   - **T015 = 第二轮运行**：13:27:13–13:27:30 全量重跑了 22 条 git 命令（首轮为 13:13）。**这是同一脚本被再次执行，不是首轮日志被篡改**（内容一致，见 §3）。
   - T002 / T003 / T065 / T097 / T008：13:29 前无新增，视为已静止。

3. **无越界写入**：任务窗口（13:09 起）内
   - `candidates/core-kummer/**` → **零文件**被修改；
   - `fact-tree/**` → **零文件**被修改。
   ⇒ 本轮无「改了 Boundary / fact-tree」的迹象（T002 首轮已查明 `registry.json` 的 ` M` 早于窗口）。

---

## 1. T002 — **UNDECIDABLE（第 3 条仍 FAIL 级）**

较第 1 轮的唯一实质变化：新增 `logs/index_check.{meta,stdout,stderr}.log`。

- `index_check.meta.log`（46 B，**全文**）：`exit=0 elapsed=0.383`
- `index_check.stdout.log`（176 B，**全文**）：`PASS: saved input hashes and shard/index match (VERIFIED_LOCAL_SHARD); no Lean replay`
- `index_check.stderr.log`：0 B

**问题**：交付方自己写明了 **"no Lean replay"**。该脚本只校验了自己存下的哈希与磁盘一致——而**这正是我第 1 轮已经独立做完的事**（114/114 全中）。它**不构成**新的独立证据。`exit=0 elapsed=0.383` 有真实进程痕迹（有耗时），这点比上轮好；但 0.383 s 也反证它确实没做任何 Lean 工作。

第 1 轮的硬问题**原封未动**：`research/core-germ-2026-10-24/` 仍是 5 份 0 字节日志 + `lean-build.log` 仅 20 行纯 axioms。
⇒ 六条门禁结论与第 1 轮相同（`#print axioms` 一条 PASS，其余 UNDECIDABLE）。

---

## 2. T003 — **UNDECIDABLE（产物形态不符门禁）**

交付物：`.tmp/{decls_dump.txt, targets.json, extract.py}` + `logs/extract.stdout.log`（50 B：`OK .tmp\decls_dump.txt`）。

- 全目录 grep `lake |lean |exit=` → **无任何 Lean 编译或退出码声明**。
- `targets.json` 内容是 mathlib 文件到声明名列表的映射（含 `Mathlib/RingTheory/PowerSeries/Substitution.lean`），属**源码静态提取**，非建构证据。
- ⇒ 本任务不声称编译，故第 2/3/4 条门禁**无对象**；第 1 条因无 `delivery.json` 不可判；第 6 条已查（无越界写入）。
- **UNDECIDABLE**：无法判断该提取结论是否正确（需要对 mathlib 侧独立复算，超出本轮范围），且缺交付清单。

---

## 3. T015 — **PASS（只读性成立）**

这是本轮唯一能给出确定判定的任务。

**（a）真正的只读核查 ✅** —— 22 条命令全部是读操作。从 `_replay.trace.log` 用正则抽出全部子命令并计数：

```
rev-parse x7 | cat-file x1 | log x1 | rev-list x2 | diff x3 | diff-tree x1 | status x1
```

**没有** `checkout` / `reset` / `merge` / `rebase` / `clean` / `stash` / `worktree` / `push` / `commit` / `update-ref` / `branch -d` 等写操作（正则扫描命中的唯一 `commit` 是 `d3c5599^{commit}` 这个 rev-parse 实参，属伪命中）。`fetch` 仅以 `--dry-run` 出现在脚本注释与本轮未执行的 `-SkipNetwork` 分支之外——实际 trace 中**没有 fetch 行**（第二轮 trace 22 行全为只读）。

**（b）网络只读性 ✅** —— `git ls-remote origin refs/heads/research/backward-paths` 返回
`d3c5599668aa57c5c00244117abd26787fcd559e	refs/heads/research/backward-paths`，与声明一致。
首轮 `git fetch --dry-run` 的 stderr（136 B）为
`From https://github.com/Luminescence10086/Inter-universal-Teichmuller-Theory` / ` * branch research/backward-paths -> FETCH_HEAD`；
**`--dry-run` 下不写 ref**。实测旁证：`.git/FETCH_HEAD` mtime = **10/24 01:46:01**，早于 T015 运行（13:13），**未被本次触碰**；`.git/packed-refs` mtime 02:32:52 同样未变。当前 `refs/heads/research/backward-paths` 仍为 `d3c5599…`、`HEAD` 仍为 `8d60456…`，与基线一致。

**（c）我上轮怀疑的 `M	research` 是伪问题** —— `git-difftree-reviewed-commit.stdout.log` 11 字节，
hex 为 `4D 09 72 65 73 65 61 72 63 68 0A`，即 `M<TAB>research`。这是 `git diff-tree`（**非递归**）对目录的正确输出：该提交只改了 `research/` 下一个文件，目录级 name-status 只显示目录名。**不是伪造，不是截断。** 配合 `git-diff-stat-reviewed-commit.stdout.log`（115 B）`1 file changed, 145 insertions(+)`，两者自洽。

**（d）一处证据标注错误（不影响只读性判定）**：`git-status-porcelain.stdout.log` 用 `--untracked-files=no`，输出恰 4 个 ` M` 条目，与脚本 `Assert-Equal 'tracked dirty file count' … '4'` 自洽。但脚本把**被跟踪文件的脏标记**也计入了，若日后新增一个 `??` 未跟踪文件，这条断言**不会失败**——属断言口径偏松，登记为改进项而非 FAIL。

⇒ **PASS**：只读性经 trace、ref 未变、FETCH_HEAD 未动三重核验成立。

---

## 4. T021 — **UNDECIDABLE ＋ 证据标注错误（新发现）**

**硬问题：`logs/build-snapshot-ThetaGermTransport.log` 文件名与内容不符。**
该文件仅 **3 行**（4662 B 是因为有超长行/CRLF，实际 `lines=3`）：

```
✔ [8771/8781] Built ContinuousKummerTheory.ContH1.Corestriction (48s)
✔ [8772/8781] Built ContinuousKummerTheory.Kummer.Corestriction (45s)
✔ [8773/8781] Built ContinuousKummerTheory.Kummer.Values (45s)
```

- 对全文检索 `ThetaGermTransport` → **NO**（零命中）。**日志从未提及 ThetaGermTransport。**
- `proj/lakefile.toml` 的 target 为 `defaultTargets = ["T021"]`，`srcDir = "T021"`；`Boundary`/`ContinuousKummerTheory` 库 `srcDir = "core-kummer-snapshot"`。快照里确有 `Boundary/ThetaGermTransport.lean`（12770 B，mtime 11:57:48，与主线同），但**该日志证明的是另外三个模块被构建**。
- 且 `✔ [8771/8781]` 这类行是 Lake 的**进度输出**，不含退出码；T021 目录下**无任何 exit-code 回执、无 delivery.json**。
- ⇒ 若交付方以这个文件名主张「ThetaGermTransport 已构建」，属**名实不符**，须改名或补真实构建记录。

另：T021 仍在 IN_FLIGHT（持续产出 olean），上述结论可能因后续补齐而变化。

---

## 5. T008 — **UNDECIDABLE（但 `RESEARCH_ONLY` 标注正确，未抬高）**

- `probe/T008Probe.lean` 首行注释明写 **`SOURCE / type-audit only, RESEARCH_ONLY`**，并声明 `This file defines nothing`。**状态标签未被抬高 ✅**（第 5 条门禁在本任务上有正面证据）。
- **`sorry`/`admit` 扫描**：命中 2 处，**全在块注释内**（L9「elaborator silently replaced their values with `sorry`」、L12「nothing here can carry a sorry」），L1–L20 为 `/- … -/` 块注释。**无活跃 `sorry`/`admit`/自加 `axiom` ✅**（第 4 条门禁 PASS）。
- 该注释还**主动披露**了 attempt1 的失败：局部 def 被 elaborator 偷偷填成 `sorry` 且丢掉 `hk/hkres` 假设，故**丢弃而不修补**——这是负责任的处置，且 `logs/attempt1.stdout.log`（22944 B）保留了失败现场。
- **门禁障碍**：`probe.stdout.log` 现为 **570 B**，但快照观测到它曾达 **32948 B**，13:25:06 被**重写成 0 → 570 B**。即 probe 仍在反复跑，当前这份 570 B 不足以支撑 `ARROW-TABLE.md` 的全部箭头。且 `probe.stderr.log`/`attempt1.stderr.log` 均 0 B，无退出码回执。
- ⇒ **UNDECIDABLE**（缺：稳定态的完整 probe 输出 + 退出码回执）。

---

## 6. T065 / T097 — **UNDECIDABLE（纯静态分析任务，形态本身不触门禁）**

- 两者全目录 grep `lake |lean |exit code` → **零命中**。均无 Lean 编译声明，故第 2/3/4 条无对象。
- T065：`trace.stdout.log`（2576 B）是一份结构化 JSON，含
  `counts: {FIELD:13, DEF_GEN:7}`、`consumers_found:13 / consumers_total:13`、`scaling_producers_found:5/5`。
  但 `def_gen_producers_are_decls` 里 **2 条为 `ok:false`**（`StripScaling.galInduced`、`StripScaling.shift_eq_zero`）——即**自报未通过项**，需交付方解释；这不构成抬高，但说明该任务结论**尚不完整**。
- T097：`logs/_verify_probe.txt` 是从 `research/round2-source-cache/*.txt` 抽的行级证据（含行号 `L2060 page=44 markerL=2041`），引文与 IUT III 官方文本（`Corollary 3.12`、`−|log(Θ)| ≥ −|log(q)|`）对得上，抽样看**引用纪律正常**。`quantifiers.json`/`sources.json` 已落盘。
- ⇒ 两者均 **UNDECIDABLE**：缺 delivery.json 与结论自证，且我未独立复算其提取正确性。

---

## 7. T049 — **IN_FLIGHT（跳过）**

30 s 内新增数百个文件、`.lake/packages/` 正在全量克隆（`tmp_pack_*` 出现又被删除）。`logs/probe01.log` 为 **0 B**。
`lakefile.lean` 声明 `require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"`——**硬编码非便携路径**（与独立重放记录 §4 指出的同一类缺陷）。
按指令记为 **IN_FLIGHT**，本轮不作判定，待稳定后复审。

---

## 8. 对 `_review/A-evidence/independent-replay-core-germ.md` 的方法学复核

**结论：方法方向正确，但该记录中的具体证据不可核验，故其自评「UNDECIDABLE → PASS」我不能背书。**

**（a）可以确认的**：
- 记录对交付方缺陷的描述与我的独立实测**完全一致**（5 份 0 字节日志、`lean-build.log` 仅 18 条 axioms 行、`port-build-exits.json` 无 argv 无耗时）。这三项我逐条复算过，**属实**。
- 我实测 `ThetaGermTransport.lean` 的**两个真实 import 均无陈旧问题**：
  - `Boundary/ProjectiveComparison`：src 11:24:44 → olean 11:26:07（fresh）
  - `TateCurvesTheta/Kummer/ThetaGermCore`：src 11:41:36 → olean 11:45:13（fresh）
  ⇒ 若 replay 真按声明执行，**不太可能被旧 olean 欺骗**（这也是该记录隐含的正确点）。

**（b）不能确认的（关键缺口）**：
- **该记录没有留下任何原始产物。** `_review/A-evidence/` 下只有 3 个 `.md`（3055 B 的那份 + 我自己的两份），**没有 replay 的 stdout/stderr、没有 `--json` 原始输出、没有 job 回执**。
- 声明「`stdout bytes: 5835`」「58 条 information / 0 error / 0 warning」「elapsed 54.9 s」全部是**叙述性数字，无文件可复算**。按我这一路的门禁口径，**叙述 ≠ 证据**——这正是我判交付方 `UNDECIDABLE` 的同一把尺子，不能对主线放宽。
- 实测反证：`candidates/core-kummer/.lake/.../ThetaGermTransport.olean` 的 mtime 仍是 **11:58:20**，而 replay 声称发生在约 12:1x/04:1x UTC。`lake env lean <file>` 在**不带 `-o`** 时确实不写目标 olean（它只写 `.olean` 若给了 `-o`），所以这**不能证伪** replay，但同时也说明**磁盘上没有 replay 的指纹**去佐证它真的跑过 54.9 s。

**（c）方法学本身的技术评估（回答问题中的三个技术点）**：
1. **`--json` 下 information 与 error 如何区分** —— 成立。`--json` 每行是一个 JSON 对象，`severity` 取值 `"information" | "warning" | "error"`；`#print axioms` 的输出以 `severity:"information"` 出现，编译错误为 `"error"`。故「58 条 information、0 error」在语义上**确实能区分**「只是 axioms 摘要」与「真有报错」。**但**：`-DwarningAsError=true` 把 warning 升为 error 这一点，须看到 `"severity":"error"` 计数为 0 才算证成；该记录给了这个数但没有原始文件。
2. **能否被旧 olean 欺骗** —— 部分能，且记录对此**没有设防**。`lean <file>` 只重新 elaborate 该文件本身，其 import 一律**读现成 olean**。所以：源文件新、import 旧 → 仍报 exit 0，但结论未必对应最新依赖。**真正的设防应是**「先对 import 做 mtime/哈希核验」或「对整包 `lake build <pkg>` 强制重编」。不过就本案而言，我实测两个 import 均 fresh，**风险实际未发生**；而 `Boundary/LaurentPoint.lean` 在 `.lake` 下**没有 olean**，说明该包确实存在「部分模块未建构」的欠账，属需要警惕的相邻风险。
3. **可否被「旧 olean 复用」整体冒名** —— 不能。`lean <file>` 若源文件有语法/类型错误必然报错，无法用旧 olean 顶替当前文件正文。故该 replay **能**证明「该 .lean 文本此刻可通过 elaborate」，这一点成立。

**（d）我的处置**：把该记录的价值限定为「对交付方缺陷的**独立确认**」（这部分我已复算属实），**不**采纳其把主线从 `UNDECIDABLE` 升为 `PASS` 的自评。若要升为 PASS，需补：`--json` 原始输出文件（或 job 回执）+ 命令 argv 数组 + 该次运行的 exit code 机器回执 + 一份 import 新鲜度核验。

---

## 判定汇总

| 任务 | 判定 | 依据 |
|---|---|---|
| T002 | UNDECIDABLE | 新增 index_check 自认 "no Lean replay"；5 份 0 字节日志未补 |
| T003 | UNDECIDABLE | 纯静态提取，无 Lean/exit 声明，无 delivery.json |
| T008 | UNDECIDABLE | `RESEARCH_ONLY` 正确、无活跃 sorry；但 probe.stdout 被重写、无退出码回执 |
| T015 | **PASS** | 22 条 git 命令全只读；refs/HEAD/FETCH_HEAD 三重未变 |
| T021 | UNDECIDABLE | 日志名 `build-snapshot-ThetaGermTransport` 与内容（3 个无关模块）名实不符；无 exit 回执 |
| T049 | IN_FLIGHT | 依赖仍在克隆；probe01.log 0 B |
| T065 | UNDECIDABLE | 静态 JSON 分析，自报 2 条 ok:false 未解释 |
| T097 | UNDECIDABLE | 行级引用抽样正常，但无 delivery.json、未独立复算提取 |
