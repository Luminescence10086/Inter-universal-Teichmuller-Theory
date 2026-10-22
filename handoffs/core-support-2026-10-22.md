# IUT 核心研究：可交给轻量 agent 的交接单

日期：2026-10-22。工作区：`D:\Inter-universal Teichmüller Theory`。

这是辅助任务包，建议使用 GPT-6 Luna 或同等级模型。四项可分别交给四个 agent，也可由一个 agent 顺序执行。先做 T1、T2，再做 T3；T4 仅做一次。不要重新调查全部 IUT 历史或构建所有外部仓库。

## 给执行 agent 的统一提示词

> 请先读本文件的公共约束，然后只执行用户分配的 T 编号。主目标是为 III Theorem 3.11→Corollary 3.12 的核心比较提供准确输入。本轮不要求你解决该争议。只修改该任务指定的输出范围；交付少量、可快速复现的文件和真实日志。成功、条件结果、失败分别报告，不能将未跑的检查写成 PASS。无需向其他 agent 发消息，也不要推送、合并或修改 fact-tree。

共同背景见：

- `research/github-iut-core-survey-2026-10-22.md`
- `research/github-iut-inventory-2026-10-22.json`
- `GAP-core-comparison-reconstruction.md`

## 公共约束与已有环境

1. 外部仓库位于 `reviews/core-round/external/`，只读。按下文固定 commit 检查；若不符，报告 `INPUT_DRIFT`，不自行切换分支或覆盖修改。
2. 不改根目录配置、现有 Lean 证明、其他任务文件、registry、现有 receipt。工作区已有其他人的未提交内容，不清理、不 reset。
3. 不运行仓库自带脚本，不执行整仓 `lake build`，不重新下载全部 Mathlib，不升级工具链。缺依赖就记录精确阻塞。
4. 不新增 `sorry`、`admit`、`axiom`、`native_decide`，不通过关闭告警使构建变绿。不得把目标不等式、`Wall`、`h312` 或等价结论装进新结构字段后声称证明完成。
5. 文献与源码整理统一标 `STATIC_ONLY`。Lean 命令行成功标 `CLI_CHECKED_EDITOR_PENDING`。只有实际编辑器检查完成才可报告编辑器状态；本任务不操作桌面，不准入 fact-tree。
6. 不能把域同构叫作 Θ-link，不能把线性自同构的扩大集合叫作原始允许重构集合，不能把抽象模型反例叫作 IUT 反例。
7. T1、T2 各以约 45 分钟为预算；T3 约 60 分钟；T4 约 20 分钟。单个证明问题连续两次修补仍失败，或一个编译进程运行 5 分钟仍无结果，就交付部分结果与 GAP，停止该分支。超时不是数学反例。不要反复重跑同一大模块。
8. 所有普通输出放在 `handoffs/core-support-2026-10-22/Tn/`，其中 n 为任务编号；目录在创建前确认不存在同名他人交付，不覆盖。T3 唯一额外源码写入路径见后文。

工具：

```text
PowerShell
Git:    C:\Program Files\Git\cmd\git.exe
Lake:   C:\Users\18746\.elan\bin\lake.exe
Python: C:\msys64\ucrt64\bin\python.exe
Lean:   leanprover/lean4:v4.34.0-rc2（已有 core-log / core-transport 项目）
Mathlib: C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib
固定 Mathlib commit: 85e3a25e006c35636f0e53b0e9296caca2685bc0
```

时间预算是停止扩展的边界，不是 PASS 条件；外部 agent 应以自己的真实起止时间填写交付。

## T1：原文定位与术语对照（优先，纯整理）

**目的：** 让高能力模型接手时直接看到争议链的原始位置，省去重复查文献。只做定位和显式依赖摘录，不判断论证是否成立。

输入：

- `research/round2-source-cache/iut-III-official-retrieved-2026-10-16.pdf`
- 同名 `.txt`。PDF 预期 SHA256：`9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9`。
- `reviews/core-round/external/LANA_report_202607/LANA_report_202607.tex`，commit `293bdd89463473ae13d40834d70fb4b7ba81da1f`。
  （勘误 2026-10-23：原稿此处为 `293bddf8…`，共 41 位十六进制、不是合法 SHA-1；实为下面这串多插了一个 `f`。以实测量 `git -C reviews/core-round/external/LANA_report_202607 rev-parse HEAD` 为准；这属文档笔误，不是 `INPUT_DRIFT`。）
- `reviews/core-round/external/MoheetBrain--iut-bridge-audit/IUT_STAGE1_SOURCE_MAP.csv`，commit `5098565e7f88e75718344702640d5d769e3f3074`。它只是已有索引线索，最终定位回原始文献。

仅定位这些单元：

1. III Remark 3.9.5(ix)：cQ3、cQ4、iQ5，以及 sQ3/sQ4/sQ5 的顺序。
2. III Remark 3.11.1：IPL、SHE、APT；只记录所在子段和显式交叉引用。
3. Cor3.12 proof：xi-d、xi-e、xi-f、xi-g。
4. LANA 的 “The main goal”“Minimal structure of the η-algorithm”“Provisional assessment”。

交付 `source-map.csv`，一行一个上述单元，列：

```text
id,source_path,source_sha256,printed_page,pdf_page_1_based,
text_line_start,text_line_end,anchor,statement_role,
explicit_references,status
```

- `statement_role` 只能选 `definition / asserted_compatibility / inference / target / assessment`；不确定填 `UNRESOLVED`，不要猜。
- `anchor` 用短定位词；不复制长段落。`explicit_references` 只记原文明确引用，推测另放 notes。
- PDF 印刷页码与文件页序分别填写；未实际核对文件页序就填 null。
- `notes.md` 最多两页，重点列“哪个结构在何时保留、哪个步骤声称忘却什么”的原文出处；区分原文陈述与你的解读。

**验收：** 索引可直接定位；source hash 正确；无“我已证明兼容性”之类升级结论。不要重新写 IUT 综述。

## T2：可复用声明卡片与直接依赖（优先，纯源码整理）

**目的：** 给后续证明提供准确的 Lean 类型和参数，不再凭 README 讨论工具。

固定仓库：

| 本地目录（相对 `reviews/core-round/external/`） | commit |
|---|---|
| `iut` | `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb` |
| `continuous-kummer-theory` | `1d5194fcc63ddeb7a8cdb6c98d59452503db60fa` |
| `tate-curves-theta` | `d1fba94861c886b671f4137ab35e24b7474c9e00` |
| `local-class-field-theory` | `a6655a871f92138e486362f08f7df48204f3e985` |

只做以下 8 张卡：

1. `Iut.Wall.EtaAlg` 与其 `realisation` 字段。
2. `Iut.Wall.EtaAlg.etaAnab_eq_etaQ_iff`。
3. `Iut.Wall.variant_of_wall`。
4. `KummerTheory.restriction_kummer`。
5. `KummerTheory.corestriction_kummer`。
6. `KummerTheory.map_section_kummer_eq_kummerValue`（核对实际全限定名称；**勘误 2026-10-23**：原稿漏掉 `KummerTheory.` 前缀，且该声明带 `include hπ in`，`hπ : Continuous π` 不出现在打印类型里）。
7. `TateCurvesTheta.TateParameter.restriction_kummer_thetaUnit`（**勘误 2026-10-23**：原稿把它列在 `continuous-kummer-theory`，实际不在该仓库——在那里 `git grep restriction_kummer_thetaUnit` 直接 exit 1；它在 `tate-curves-theta` 的 `TateCurvesTheta/Kummer/ThetaValues.lean`，且带隐藏前提 `[CompleteSpace K] [IsUltrametricDist K]`）。
8. `PadicField.eq_artin_of_forall`。

每张卡记录：仓库 SHA、文件与行号、文件 SHA、直接 import、声明原始签名、作用域 variable/typeclass/局部实例、声明显式使用的前提、输出是什么。若只摘 theorem 那一行漏掉 section 参数，卡片不完整。

另输出 `edges.csv`，列 `from,to,kind,source_location`。只列这 8 张卡的直接关联；`kind` 区分 `import / signature_reference / proof_reference`。这不是完整传递依赖闭包，不扩展成全仓图。

输出 `cards.md`、`cards.json`、`edges.csv`。不下载、不移植、不构建这四个大工程；也不自动认定任何前提已由原始 IUT 满足。

**验收：** 八张卡可追溯到固定源码，所有状态 `STATIC_ONLY`；“工具需要什么”清楚，不额外声称证明成立。

## T3：把两份字面对数定义接起来（小型 Lean 任务）

**目的：** 消除已移植工具之间的定义重复，并将已有 Q3 收敛结论接到运输工具实际使用的对数。这是局部工具接线，不探索核心新证明。

只读输入：

- `candidates/core-log/PadicLogVolume/PadicLog.lean`
- `candidates/core-log/CoreLog/QpThree.lean`
- `candidates/core-transport/CoreTransport/Basic.lean`
- `candidates/core-transport/CoreTransport/Completion.lean`
- 两工程的 toolchain、lakefile、manifest；开始前记录 hash。

唯一允许新增的 Lean 源码：`candidates/core-transport/DelegatedLogBridge.lean`。若已存在，停止并报告，不覆盖。现有文件一律不改。

建议以这两个 import 开始，使用新命名空间 `DelegatedLogBridge`：

```lean
import CoreTransport.Basic
import CoreLog.QpThree
```

按顺序尝试三项：

1. 在实际 `ℚ_[3]` 上证明 `CoreTransport.localLog x = PadicLogVolume.padicLog x`，通过展开已有定义核对项、指标和类型；不能重新定义其中一个函数。
2. 当 `‖x - 1‖ < 1` 时，以第一项和已有 `CoreLog.principal_unit_log_hasSum` 推出同一项级数的 `HasSum ... (CoreTransport.localLog x)`。
3. 以第一项和已有 `CoreLog.principal_unit_log_image`，得到 `CoreTransport.logImage ℚ_[3]` 与已有闭球的精确相等。

第 1 项是定义层接线，不把它包装成数学创新；第 2 项必须真正使用收敛证明，不能只用 totalized `tsum` 的默认值。不得从另一个范数模型偷换到 Q3 原生范数。

编译入口，在 `candidates/core-transport` 工作目录执行：

```powershell
& 'C:\Users\18746\.elan\bin\lake.exe' env lean -DwarningAsError=true DelegatedLogBridge.lean
```

在文件末尾对实际完成的三项 `#print axioms`。保存完整 stdout/stderr 和真实退出码；只允许标准 `propext`、`Classical.choice`、`Quot.sound` 的子集。不要改公共 import root，不跑 `lake update`；缺失 `.olean` 就列具体缺项，交回主线决定。

第 1 项成功后其余失败，可以只交付第 1 项。成功模块不能残留失败证明。失败目标与报错保存在 T3 输出目录的 `GAP.md`，同时在根目录新增 `GAP-delegated-T3-log-bridge.md` 作简短指针。不要修整数环实例问题、尾项误差或新增 Galois/Θ-link 实例。

**验收：** 一个新增源码、一个命令、真实 exit 0、零 warning/error、实际 axioms 输出、输入未变。编辑器状态保持待验，不自行修改 fact-tree。

## T4：现有候选的一次小范围复现（最后做，无需创新）

**目的：** 给主线一个可快速核对的冻结交付。已有结果不要反复冷构建。

先读 `research/core-log-extraction-2026-10-22.json` 与 `research/core-transport-checks-2026-10-22.json`，核对其中 source/log hash；不存在的记录或没有记录的源文件自行补记 hash，不假定已经核验。

确认所需既有 `.olean` 可用后，只编译以下 3 个入口，不写 `-o`，不重编完整上游模块：

```powershell
# 工作目录 candidates/core-log
& 'C:\Users\18746\.elan\bin\lake.exe' env lean -DwarningAsError=true CoreLog/QpThree.lean

# 工作目录 candidates/core-transport
& 'C:\Users\18746\.elan\bin\lake.exe' env lean -DwarningAsError=true CoreTransport/Completion.lean
& 'C:\Users\18746\.elan\bin\lake.exe' env lean -DwarningAsError=true CoreTransport/AxiomExports.lean
```

每次单独运行，捕获两条输出流和退出码。输入源码在前后 hash 一致；每个进程最多 5 分钟，超时记 `TIMEOUT`，不要换更长上限反复尝试。不要修改原日志；新日志只存 T4 目录。T4 不编译 T3，避免并行期间对未冻结输入验收。

交付 `replay.md` 与公共 `delivery.json`；不写额外审计框架、不改 pin、不修已有证明、不操作桌面。源码变化记 `INPUT_DRIFT`；依赖缺失记 `BLOCKED_DEPENDENCY`；不要用旧日志代替本次结果。

**验收：** 三个具体命令的进程结果、源码 hash、完整日志；一次即可。此任务只确认命令行复现，不能关闭任何 IUT GAP。

## 公共交付格式：让接收方几分钟内判断能否接纳

每个 T 目录只需本任务文件、日志和 `delivery.json`，再加最多 20 行 `SUMMARY.md`。JSON 用普通字符串/数字/数组即可，示意：

```json
{
  "task_id": "T3",
  "status": "CLI_CHECKED_EDITOR_PENDING",
  "started_at": "实际带时区时间",
  "finished_at": "实际带时区时间",
  "inputs": [{"path": "相对工作区路径", "sha256_before": "真实SHA256", "sha256_after": "真实SHA256", "commit": null}],
  "outputs": [{"path": "相对工作区路径", "sha256": "真实SHA256"}],
  "commands": [{"cwd": "相对工作区路径", "argv": ["实际可执行文件", "参数"], "exit_code": 0, "timed_out": false, "log": "日志路径"}],
  "completed": ["具体完成项"],
  "open": ["未完成项"],
  "editor_status": "NOT_CHECKED",
  "fact_tree_admitted": false
}
```

允许状态：`STATIC_ONLY / CLI_CHECKED_EDITOR_PENDING / PARTIAL / INPUT_DRIFT / BLOCKED_DEPENDENCY / TIMEOUT`。未执行命令时 `commands` 为 `[]`；没有退出码时填 null，绝不填 0。JSON 中的状态是索引，不是证明；接收方仍查实际源码与日志。

接收时只需：核对交付文件/源码 hash，抽查 T1/T2 的关键位置，重跑 T3 的单一入口；T4 对无变化输入不再重复全套。正式 fact-tree 准入仍须主线安排一次实际 VS Code 零诊断检查。

## 本批次不外包给轻量模型的工作

- 判断 cQ3/cQ4、SHE/IPL/APT 是否足以推出原始 xi-f。
- 构造原始相关联的 Ind1/2/3 witness，或证明模型与原算法忠实对应。
- 推导新的全局体积估计、寻找核心反例、判断争议已解决。
- 将现有条件链或局部交换图升级为原始 Cor3.12 / abc 证明。

这些属于主线探索。辅助任务即使全部完成，核心 GAP 也保持 OPEN。
