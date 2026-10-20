# 第八轮（我方第三轮）：检验「检验器」的工具四件套

日期：2026-10-20（Asia/Shanghai）。基线 `b8f2566`（73 条准入、schema-3 receipt 有效）。
分支 `research/round6-bridge`。**本轮不新增数学定理**，全部产出是新工具与其自测；
目标是让"门禁是否真的会拦"从信念变成可执行证据，并把本会话两次被同一类问题绊住的
经验固化成工具。

## 迁移来源与本轮工具

| 工具 | 迁移自 | 解决的真实痛点（本会话实证） |
|---|---|---|
| `audit/affected.py` | 增量构建的 affected-targets / CI 路径过滤 | 每轮 Astra 要手算"哪些证据作废"；我这次也靠手算列了 5 个提交的影响面 |
| `audit/mutation_harness.py` | 变异测试（PIT）／故障注入 | 负测此前是一次性的手写实验，无法回归；且从未系统性检查"哪些门禁其实拦不住" |
| `audit/claim_index.py` | doctest／文学化测试／SBOM 溯源 | 审阅者找到的 S1–S6 全是"文档超出 Lean"，只能人工逐句读 |
| `audit/tcb_manifest.py` | 最小可信基（TCB 最小化）／SLSA 范围声明 | pin 过宽：我两次因为改了 `tools/` 里的工具而作废真实编辑器观察 |

四件套均 **stdlib-only、确定性输出、只读仓库**；全部写在 `audit/`，因此**不在任何
receipt 的 pin 集内**（见下），提交它们不会作废 73 条准入。

## 实测数字（真实仓库，非夹具）

**`audit/affected.py`**（`--range 78bc059..HEAD`）：387 个文件 → 3/3 receipt 作废、
10/10 合同需重审、135 节点中 73 条退回 pending。
单文件示例 `--files bridge/IUTBridge/Admissibility.lean`：bridge receipt 作废（73 条准入归零）、
14 个直接节点 + 2 个传递依赖（`IUTBridge.Integration.*`）、合同 BR-03/04/06（+BR-10 经传递）
失效、6 条"有风险"、该文件内有 20 个被 pin 的语句名——即"必须用语句锁再判语义，哈希判不了"。

**`audit/mutation_harness.py`**：M1–M8 × 7 门禁矩阵，**所有声称会被拦的变异都被拦到**；
26 条测试把每处"设计性盲区"也断言下来（否则会悄悄退化成"什么都拦"）：

| 变异 | 拦截者 | 备注 |
|---|---|---|
| M1 加前提 / M2 改界 / M4 加公理 / M6 删节点 | 语句锁 + 语义锁 | 输入哈希**拦不住**（导出是被刷新的产物，不是输入） |
| M3 假设数漂移 | 假设审计 | 这正是本轮之前两套验证器都缺的那一项 |
| M5 定义体 ∃→∀（类型不变） | 语义锁 + 合同体门禁 | 语句锁**拦不住**——这是 F4 存在的理由 |
| M7 输入字节漂移 | 输入哈希 + 清洁检出 | 两把锁都拦不住 |
| M8 负对照（仅改注释） | 输入哈希 | **不被判为语句漂移**，证明锁不是"凡改必红" |

**`audit/claim_index.py`**：26 篇文档、410 条"机器事实型"断言 → 已锚定 11、显式 narrative 0、
**未锚定 399**、悬空 0。最差：`research/round6-results.md` 46/46、`bridge/README.md` 0/7；
唯一达标面是生成的 `bridges/index.md`。75 条只差"缩写 → 全限定名"，`--fix-hints` 可机械修。

**`audit/tcb_manifest.py`**：三个工程**都没有 under-pinned**（没有"读了却没 pin"的隐性证据缺口），
问题全在 over-pinned 一侧，且集中在 bridge：

| 工程 | pinned | 真正被解读 | over-pinned | 受影响准入 |
|---|---:|---:|---:|---:|
| root | 16 | 13（11） | 2 | 38 |
| local-field | 15 | 12（10） | 2 | 24 |
| **bridge** | **36** | **26（15）** | **20** | **73** |

bridge 的 20 个 over-pinned 里 **19 个是工具文件**（`tools/*` 15 个 + `bridge/tools/*` 4 个）——
"改任一个无关工具就作废 73 条准入"。`--propose` 给出的收窄 pin：bridge 16 / root 14 / local 13，
每项附"从未被解读"的理由，且不写盘。

## 一个诊断（把上一轮的"卡死"结清）

`tools/semantic_lock.py` 不是死锁，是**每次都无缓存地重新 elaborate** `tools/DefinitionBodies.lean`：

| 工程 | DefinitionBodies 实测 | freshness 深检 |
|---|---:|---:|
| main | 88.9 s | 47.2 s |
| local-field | ≥150 s（超我设的 150 s 观察窗） | 19.9 s |
| bridge | 161.2 s | 21.3 s |

合计 ≈ 6–7 分钟纯 Lean 展开，加上深检共 ≈ 8–9 分钟，超过我上一轮给的 600 s 命令上限，
所以表现为"卡死"。修复方向：把它做成 Lake 构建目标（有 olean 缓存）或惰性化；
但 `tools/*` 被 pin，**修复必须与下一次编辑器观察同批落地**，否则 73 条准入归零。

## 诚实的边界

- `claim_index` 只证明"这句话指向一个真实定理 id"，**不判断措辞是否忠实**：
  "严格递增"挨着一个反单调定理仍算已锚定。S1–S6 那类缺陷仍需人/模型逐句对读
  `statement` 与文字；它给的是**召回下限**与可计数指标，不是证明。
- `mutation_harness` 检验的是**门禁**，不是数学。它断言了若干"漏"是设计使然
  （导出刷新、语句相同），因此不能把"矩阵全绿"读成"证据链完备"。
- `affected` 看到的是文件级影响；`facts.json` 的 `node.sha256` 在三个工程里都等于源文件摘要，
  所以**语义是否变化只有语句锁能答**。
- `tcb_manifest` 是静态发现：动态路径一律列 `UNRESOLVED` 并以退出码 3 报警，不静默宣称完备。

## 请 Astra 决策的三件事

1. **是否采纳收窄 pin**（bridge 36 → 16）。收益：工具修复不再作废真实观察；代价：pin 变紧，
   新增被解读的输入时必须同步扩 pin（工具会报 under-pinned）。
2. **`audit/` 是否纳入下一轮 pin**。现状是"不在 pin 内"（因此本轮提交不作废准入）；
   若认为审计工具本身决定证据强度，应在下一次观察时一并纳入。
3. **是否把 `claim_index --strict` 作为文档门禁**。当前 399 条未锚定会让它红；建议分两步：
   先 `--fix-hints` 修 75 条机械项，再把"新增文档必须锚定"作为增量门禁，而不是一次性清债。

## 复现

```powershell
python audit\affected.py --range 78bc059..HEAD
python audit\mutation_harness.py
python audit\claim_index.py --strict
python audit\tcb_manifest.py --propose
python -m unittest discover -s audit\tests -p "test_*.py"   # 65 tests, OK
```

## 未关闭

G01–G06 与 RI-01–08 仍全部 open；Corollary 3.12、abc 未证；未构造任何 IUT 对象。
上一轮遗留：`main` 的 F1 字节修复待合并；两项 Lean 侧措辞待下次观察同批修。
