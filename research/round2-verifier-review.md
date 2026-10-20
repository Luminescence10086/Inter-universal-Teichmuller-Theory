# 第二轮：验证器独立审计

审计日期：2026-10-16，Asia/Shanghai。范围：只读生产 `tools/verify.py`、`Export.lean`、`query.py`、`EditorCheck.lean`、receipt、日志、facts 与第一轮研究文本；在 `.tmp-round2-verifier/` 运行自建最小测试，未执行外部第三方代码，未修改生产工具。该临时目录的 receipt 明确标记 **SYNTHETIC TEST ONLY**，不能作为真实 VS Code 验收证据。

基线 `tools/verify.py` SHA256：`03461da06f12c52026fb29caa63a0f1511dee19c3b1b9d139da9ef82b961ac17`。以下行号对应此基线，后续修复可能移动行号。

## 结论及优先级

发现一项完整复现的 P1：经辅助 `def` 的定理依赖被漏掉，导致已准入节点间依赖图漏边，且可绕过“不得依赖尚未编辑器验收的本项目定理”门禁。另有哈希快照、导入闭包、工具身份、输出通道及编辑器证据绑定方面的限制。**这些是准入系统和证据工程问题，不是 Lean 内核证明了错误数学命题。** 当前 12 项模型定理的数学陈述没有因此被证伪。

| 编号 | 优先级 | 问题 | 当前证据 |
| --- | --- | --- | --- |
| R1 | P1 | 只取直接常量后与公开 theorem 集相交，漏过辅助定义/辅助证明 | 临时完整 verifier 实测 `Admitted=1,pending=1`，已准入 B 实际经 def 使用未准入 A |
| R2 | P1 | 没有固定受检查输入快照；编译、导出和最终哈希可能对应不同版本 | 静态检查执行次序；未刻意对生产文件制造竞态 |
| R3 | P2 | 导入闭包、标准库实体、验证工具未进入 receipt/query 的哈希上下文 | 临时改 Export.lean 后 query 仍接受；工具链只检查版本子串 |
| R4 | P2 | 硬编码文件列表及正则声明发现不完整，未登记模块可作为库常量漏过 | 静态可复现语法例；不代表当前 12 项已漏掉实际公开 theorem |
| R5 | P2 | `run()` 不检查 stderr，build 不要求零诊断 | 当前生产日志 stderr 均空；这是未来失败模式 |
| R6 | P2 | receipt 是人为断言；观察文本未被哈希和验证器绑定 | 已有文档诚实说明其非密码学证书；机器门禁仍只验证布尔值/计数/非空说明 |
| R7 | P3 | query 信任 facts 的结构与内容，无独立 schema/完整性检查 | 本地手改 facts 的可信边界未被完整定义 |

## R1：间接依赖被抹掉，准入闭包失效

`Export.lean:13` 仅访问 `info.type.getUsedConstants` 和 `info.value.getUsedConstants`，不递归展开这些常量。`verify.py:89` 仅做 `constants ∩ declarations`。因此 B→helper→A 的第一条边不是公开 theorem 时，A 不会成为 B 的 `depends_on`。`verify.py:98` 的已验收依赖检查由此也看不到 A。

已在临时目录完整复现：

```lean
-- IUTAudit/Scale.lean
import Std
namespace IUTAudit.Scale
theorem hidden_base : True := True.intro
end IUTAudit.Scale
```

```lean
-- IUTAudit/Descent.lean
import IUTAudit.Scale
namespace IUTAudit.Descent
def hiddenHelper : PLift True := ⟨IUTAudit.Scale.hidden_base⟩
theorem visible : True := hiddenHelper.down
end IUTAudit.Descent
```

临时 receipt 仅给 `Descent.lean` 的合成测试记录，`Scale.lean` 完全没有记录。运行原验证器，得到：

```text
Lean zero-diagnostic source checks passed. Admitted=1, pending=1.
IUTAudit.Descent.visible
  constants = [True, PLift.down, IUTAudit.Descent.hiddenHelper]
  depends_on = []
  status = admitted
```

`hidden_base` 属于待编辑器验收定理，`visible` 却准入，故是准入门禁的真实反例。最初以 `def hiddenHelper : True` 尝试时，`linter.defProp` 正确阻止；上面的 `PLift` 包装是零诊断的最小修正版，说明不能依赖该 linter 补上图遍历。

**修复建议**：在 elaborated environment 上访问所有常量种类的 type 与可用 value，递归穿透 def、opaque、私有与自动辅助项，直到遇见登记的公开 theorem 节点；把首次到达的这些节点作为压缩图边，并继续对它们分别验收。保留完整的底层常量依赖图或路径证书，例如 `visible → hiddenHelper → hidden_base`。不要只递归 `.thmInfo`；上例 helper 是 `.defnInfo`。对所有可达常量继续做公理审计；遇到缺失环境实体应失败关闭而非忽略。

这里必须区分“图可追溯性”与“数学必需性”：proof term 引用 A，只表示当前证明实现使用 A；并不证明任意证明 B 都必须使用 A。图也不应把不可见的某条数学依赖猜测成已实际发生的边。

**对当前数据的有限复核**：现有 export 中有 17 个 theorem rows、正式树有 12 个节点。只在已导出的 theorem rows 间递归，没有发现额外的登记 theorem 路径；此检查不覆盖尚未导出的 def 实体，不能宣称已完成完整常量闭包审计。现有 `_proof_1_1` 说明自动辅助项确实存在，不能假设将来不会在其中出现项目 theorem。

## R2：编译字节与登记字节可能不同

基线执行次序：`lake build`（57）→读源并直接检查（60–68）→从构建产物导出（69）→读 receipt（79）→计算 context hash（80）→逐文件计算 source hash（88）。直接检查没有显式把本次检查产物用于 Export，Export 导入的是构建得到的模块。

最小竞态时间线：build 得到版本 A；源文件改成 B（保留相同定理名字）；直接检查 B；Export 仍读 A 的 `.olean`；receipt 和最终 hash 都对应 B。结果可能把 A 的陈述登记到 B 的源文件 hash。另一个窗口是最终哈希读取后到 facts 写入前源文件改变。query 随后可能发现部分更改，但不能把先前错误的运行证据变成正确证据。

**修复建议**：开始时固定源文件、导入闭包、工具和上下文的完整快照；在隔离的只读内容快照上构建与导出，或至少在开始/每个关键阶段/结束做一致性校验并失败关闭。让 `.olean` 与源文件、编译参数和 toolchain 实体的指纹关联。结束时原子发布整个 facts 结果；竞争验证进程采用锁或独立 run 目录，避免互相覆盖日志和状态。普通前后哈希能检测常见变化，但不能抵抗刻意的 ABA 改动；应把此限制写入威胁模型。

此处未在生产树强行制造竞态；结论限于执行流程允许不一致的输入窗口，不宣称当前日志实际遭遇过它。

## R3：哈希覆盖与 toolchain/import 的可信边界

`CONTEXT` 只含 5 个路径。未含 `verify.py`、`Export.lean`、`query.py`、receipt/观察文本，也未包含实际 Lean 二进制、Std/Lean 模块、`.olean` 与源码闭包。版本校验仅匹配 `version 4.34.0,` 子串；输出里的 commit 虽被保存，却没有与预期值比对。Lake manifest 无包不等于没有标准库依赖。

临时复现：在已生成临时 facts 后，仅向临时 `tools/Export.lean` 添加一行注释，运行临时 `query.py visible`，仍打印已准入结果。注释不改变数学；它证明查询没有绑定导出器的身份。若将来修改导出逻辑、标准库安装或可达模块，仅现有上下文哈希不能判定旧产物是否适用。

**修复建议**：记录并核对准确 Lean commit、平台、实际 executable 路径与二进制身份；列出从当前实际导入环境得到的模块闭包及对应源码/产物哈希。明确标准库作为预先信任工具链的一部分还是逐模块验收，两者不可含混。工具和验证政策也加入 run manifest，并给产物 run_id、manifest hash。query 检查当前政策/工具指纹与产物一致，变化时要求重验。

用户要求被纳入节点逐项通过 VS Code，未必要求把标准库所有常量也变成节点。应将“可信工具链依赖”“已验收项目节点”“未验收外部候选”区分清楚；导入闭包的身份锁定不能被“库常量不是节点”这句话替代。

## R4：文件与声明发现策略只适用于当前非常窄的源风格

`SOURCES` 固定为两文件；`^theorem\s+(\w+)` 不识别下面这些声明：

```lean
@[simp] theorem tagged : True := True.intro
protected theorem protectedName : True := True.intro
private theorem privateName : True := True.intro
```

多层 namespace、`section`、Unicode 标识、转义标识和新模块也不宜依赖首个 namespace 正则定位。大多导致遗漏或失败关闭，而不是直接伪造定理；但一旦被遗漏声明经 helper 用于已登记 theorem，它会削弱准入闭包。新增但不可达文件本身不应使旧定理失效；新增且可达模块必须进入闭包和来源映射。

**修复建议**：用 Lean 的 environment/source/module 元数据、命令级 declaration ranges，或人工明确的目标登记清单核对实际环境，不用正则猜测命名。登记清单应和所有可达项目声明对账，并为未准入者给显式状态。未登记的私有/自动项可以作为图的内部节点压缩，不必强迫把每个自动项作为用户节点。

## R5：stdout 空不保证 stderr 空

`run()` 保存 stderr，但只在 returncode 非零时拒绝；正常返回仅把 stdout 传回检查者。于是退出码 0、stdout 空、stderr 有告警的工具输出仍通过“空诊断”门禁；`lake build` 的 stdout、stderr 甚至未要求零 warning。

可复现的通用子进程：`python -c "import sys; sys.stderr.write('warning: probe\\n')"` 会退出 0。这里不把任意 stderr 文本都解释成 Lean 告警；问题是系统并未分类检查第二个输出通道。当前生产 `build.json`、`scale.json`、`descent.json` 的 stderr 均空，没有证据说当前 12 个节点因此失格。

**修复建议**：run 返回完整结果；对证明检查与导出要求 stderr 空，或对已知工具噪声采用明确的白名单分类。构建必须有 warningAsError 或结构化日志审计；所有信息、警告、错误分开记录。`errors="replace"` 应记录解码替换发生情况，防止损坏字节被悄悄当成无害文本。

## R6：真实 VS Code 观测的证明力及绑定方式

当前 receipt 声称两源码已打开、Lean server 已检查，并保存 0 error/0 warning；观察文本展示 EditorCheck 窗口、12 项 `#check` 和 Problems 的 24 information。README 已诚实说明它只是观察记录，**没有必要把这个限制描述成造假或密码学漏洞**。

但验证器不读取 `evidence` 文件内容，不校验其 hash、不检查 observer/observed_at，也不确认 EditorCheck 实际逐项覆盖当前登记节点。非空 `observation` 加布尔值足以放行。临时测试 receipt 正是合成的，验证器无法辨别；这是人工可信输入的边界，不是 Lean 的认证。

此外，打开 `EditorCheck.lean` 并 `#check` 导入 theorem，主要证明声明可解析；它可以读取 `.olean`，本身不重新检查源证明。为满足用户“在 VS Code 跑一遍”的要求，需要保留两源文件对应版本确实由 Lean server 完成处理且无诊断的观察，而非只看导入文件中的名字可用。当前文字声称已完成，但机器没有独立验证这段操作。

**修复建议**：receipt 绑定完整 manifest、run_id、精确文件版本、实际编辑器 toolchain/server 信息、检查完成状态、当前全部目标列表及 observation hash；保留带时间的 UI 截图或原始 accessibility 观察和 Problems 状态。解析并核对目标覆盖；receipt 失效时降为 pending。仍应明确观察者是可信人工/代理输入，无法仅靠 JSON 布尔值独立证明真实 UI 过程。

## R7：query 的边界与原子产物

query 检查 `status=checked` 以及 facts 自己列出的 context/source hashes，但不验证必需路径集合、节点唯一性、edges 与 depends_on 一致性、准入依赖闭包或产物来源。若误删 context 条目，检查会变少；如果手改 statement 而保留 source hash，查询会照印。当前 facts 并无这样的证据。

**修复建议**：增加 schema 版本和严格结构校验、必需 manifest 集合、唯一 ID、edge closure 和 dependency 状态检查；将 facts 与 manifest/日志关联并原子写入。不能用与 JSON 同放可写目录的自报 hash 宣称防篡改；应把目的限定为发现意外损坏和版本漂移。

## 第一轮数学文本与模型边界

已核读 README、GAP、controversies、core-and-bridges 和两份 Lean 模型。边界总体清楚：

- README 明确 12 项只是通用机制模型；未定义真实 Hodge theaters、Θ-link 或 Arakelov 体积。
- Scale 的整数不等式前提没有被包装成 IUT 已证结论；Descent 的充分条件明确要求提供 section，没有声称任意映射自动存在 section。
- controversies 把 SS、望月、LANA、Joshi、Dupuy–Hilado、Urahigashi 的主张与本项目已验收定理分开，未声称穷尽所有反对意见。
- core-and-bridges 的九方向是候选命题，含失败判据与语义桥接义务，未当作补救已完成。
- GAP 保留 G01–G06，且多次说明未证明 Corollary 3.12 或 abc。该审计不复核这些外部论文的数学正确性。

需要修订的一句话是 README 对 graph 的描述。当前实现只能保证“直接 term 中可见且符合正则登记的 theorem 引用”，不能写成经辅助项压缩后完整的项目 theorem DAG；修复 R1 后才可作此承诺。另应将“任一工具链变化均会检测”限于当前实际锁定的字段，或先补 R3。未来引用外部论文时维持现有“作者声称/未在本项目验证”的措辞即可。

## 修复后的最低回归清单

1. R1 的 PLift 例中，A 无 editor receipt 时 B 必须 pending 或整体拒绝；补齐 A 后显示 A→B，并保存 helper 路径。
2. `@[simp] theorem`、私有 helper、自动 `_proof_...`、可达新增模块均有明确发现/内部节点策略。
3. 证明输入在 build、export、最终发布之间变化会失败关闭；旧 facts 不会继续以 checked 暴露。
4. stderr 非空、非预期 warning、工具版本/manifest/导入实体改变会触发相应拒绝或重新验收。
5. receipt 缺失、目标漏检、版本不符、观察文件缺失/哈希不符均不得正式准入。
6. 当前 12 项在最终固定工具下重新编译、公理审计和真实 VS Code 验收；只有完成后恢复 admitted。不能把本临时测试中的合成 receipt 带回正式树。

本审计新增的是验证工程修复义务；没有新增任何关于真实 IUT 正确或错误的数学结论。
