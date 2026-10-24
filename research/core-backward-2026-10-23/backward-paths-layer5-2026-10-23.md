# 倒推第五层：执行指令级，与现有六条路径的比对

日期：2026-10-23。性质：**设计 + 已实测的两条结果**。实测部分标 `MEASURED`，其余仍为设计。
核心 GAP 保持 OPEN。

前置：`backward-paths-layer34-2026-10-23.md`（D0–D7）、`backward-paths-layer2-2026-10-23.md`（V1–V6）。

---

## 5.0 本层先落两条实测（`MEASURED`）

把 D0 的验收命令真跑了一遍，结果两条都很要紧：

| 命令 | 结果 | 后果 |
|---|---|---|
| `lake build`（无参） | exit **0**，但输出 `warning: no targets specified and no default targets configured` / `Nothing to build.` | **这种"通过"是空的**。`core-transport` 的 lakefile 里 `lean_lib CoreTransport` 没有 `@[default_target]`，所以无参构建什么都不做。任何"构建通过"的交付若用这条命令，等于什么都没验 |
| `lake build CoreTransport`（显式目标） | exit **0**，`Build completed successfully (2672 jobs)`，3.4 s | 真构建成功；但这次**命中本地 `.lake` 缓存**，冷缓存/干净克隆未验 |

由此确定一条硬规矩：**验收命令必须写显式目标；"nothing to build"一律记 FAIL，不记 PASS。**

### 另外发现：四个候选包把 mathlib 指到了本机绝对路径

| 包 | `lakefile` 里的 mathlib 来源 | 能否被他人构建 |
|---|---|---|
| `candidates/core-transport` | `require «core-log» from "../core-log"`（相对路径，✓） | 取决于 core-log |
| `candidates/core-log` | `require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"` | **不能** |
| `candidates/core-compactness` | 同一条绝对路径 | **不能** |
| `candidates/nonarchimedean-ring` | 同一条绝对路径 | **不能** |
| `candidates/pilot-shadow` | `path = "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"`（toml） | **不能** |
| `candidates/core-normalization` | **没有 lakefile** | 不能按包构建 |
| `candidates/core-order-bridge` | **没有 lakefile** | 不能按包构建 |

（以上由 `git grep -n 'C:/Users' origin/candidates/restore-local-only -- 'candidates/*lakefile*'` 直接核出，
是**已提交内容**的实况，不是本地观察。）

所以 `core-transport` 虽然自己能构建，但它经 `core-log` 传递依赖一个**只存在于本机的桌面路径**。
干净克隆后必然失败。这不是"补文件"能解决的，要改成 `require mathlib`（走 lake 正常解析）或相对路径。

补充更正：`core-transport` 是唯一**缺 `@[default_target]`** 的那个（所以它的无参 `lake build` 空转）；
`core-log`、`core-compactness`、`nonarchimedean-ring` 都有 `@[default_target]`。
"无 default target"与"绝对路径"是两个独立缺陷，不要混成一条。

---

## 5.1 五个执行单元（E1–E5）

第五层把 D0–D7 收敛成五个"第一次提交就能判生死"的单元。每个单元定义成：落点 / 第一条命令 / 第一个失败信号。

### E1｜候选可复现验收脚本（对应 D0）

- 落点：`tools/check_candidate_build.py`（新文件，不动既有工具）。
- 第一件事：对 `core-transport`、`core-log`、`core-compactness` 逐一跑 `lake build <显式 lib 名>`。
- 外加三条静态检查：**lakefile 里不得出现 `C:/Users/...` 绝对路径**、`lean-toolchain` 必须存在、
  `lake-manifest.json` 必须存在。
- 第一个失败信号：任一包的 `lake build` 输出含 `no targets specified`（说明没真构建）或退出码非 0。
- 判据：五个目录各产出一行 `PASS / FAIL / LOCAL_ONLY`，且 FAIL 必须附首个错误行。

### E2｜`logBridge` 草案（对应 D1）

- 落点：`candidates/core-log/CoreLog/LogBridge.lean`（放在 core-log 内，因为它已经有 `PadicLogVolume` 与 `localLog` 的使用方）。
- 第一条命令：`lake env lean -DwarningAsError=true CoreLog/LogBridge.lean`。
- 第一个失败信号：定义域必须在"加法性"与"与范数相容"之间二选一。若两者不能共存，立刻停，别继续写定理。
- 判据：文件里必须同时出现 `logBridge` 的定义、加法性定理**或**其否证、以及一对 `x, y` 的乘性反例。

### E3｜Mathlib 侧检索（对应 D2）

- 落点：`research/core-backward-2026-10-23/mathlib-log-series-search.md`。
- 第一件事：检索 Mathlib 是否有 `Real.log` 的幂级数展开（本文**不假设**存在）。
- 第一个失败信号：检索做不出"有/无"的确定结论（例如只给"我没找到"）。**"没找到"不算结论**，必须给出检索词、检索范围、命中清单。
- 判据：文档必须能回答"`localLog` 在 `K = ℝ` 下与 `Real.log` 的关系，是否已有现成引理可调"。

### E4｜权重参数化（对应 D4/D5）

- 落点：`candidates/core-transport/` 下受影响文件 + 一份 `weight-parameterization.md`。
- 第一件事：`grep` 出所有出现"全局 log-volume""the paper's weights"却不带参数的句子，计数。
- 第一个失败信号：计数不为 0 就交付 → 退回。
- 判据：改后计数为 0；且给出两个不同 `w` 导致结论不同的实例。

### E5｜两个反例（对应 D6/A7）

- 落点：`candidates/core-order-bridge/`、`candidates/core-normalization/`（都缺 lakefile，先补 lakefile 再谈）。
- 第一件事：给这两个包补 lakefile + lean-toolchain + manifest（否则它们连"能跑"都谈不上）。
- 判据：反例可重放；`c` 与 `S` 的关系二选一必须写明。

## 5.2 依赖与并行度

```text
E1（验收）─── 必须先做，否则后面所有"通过"都可能是空的
   │
   ├─→ E2（logBridge）──→ E3（Mathlib 检索）
   ├─→ E4（权重参数化）
   └─→ E5（补 lakefile，然后两个反例）
```

E2、E4、E5 在 E1 之后可并行；E3 跟在 E2 后面。

---

## 6. 与现有六条路径的比对

### 6.1 逐条比对

| 路径 | 第一层的说法 | 第五层落实后的实际状态 | 现在能不能开工 |
|---|---|---|---|
| **P6** 把 (9-1) 当输入 | "不占工期" | 不需要 D0–D7 任何一件；只需把 `EtaAlg` 的等式变成显式 `hypothesis` | **能，且是唯一不依赖任何修复的路径** |
| **P2** 近似输出 | "P1 失败时的唯一退路" | 需要 D1（logBridge）；`core-log` 现在入库但**指死本机路径**，先要 E1/E5 修 | 能，但第一个命令是 E1 不是 E2 |
| **P1** 精确对象 | "主线" | 需要 D1、D6、D7；其中 D7（`c` 与 `S`）排在最后 | 能，但顺序被拉长 |
| **P3** 紧致 | "P1 卡住时接手" | `core-compactness` 已入库且有 `default_target`，但 **mathlib 指死本机绝对路径** ⇒ 之前"CLI 候选已通过"在他人机器上不成立 | 先改 mathlib 来源，再谈紧致 |
| **P4** 下降/群胚 | "独立探针" | 障碍类系数依赖 D4/D7，两者都还没做 | 暂时不能 |
| **P5** 弱化 | "风险最高" | 与 P2 共享 D1；差别在是否要求"真实允许输出" | 能，但应排在 P2 之后 |

### 6.2 三处需要改写的判断

**改写 1（顺位）**：第一层第 4 节说"先做 G3 台账，P1 与 P2 并行"。第五层实测后必须改成：
**先做 E1（验收脚本），因为在此之前任何"构建通过/候选已验收"都可能是 `Nothing to build` 造成的假象。**
这是实测推翻排序判断，不是补充。

**改写 2（可行性）**：第一层把 P3 的紧致性工具当作已有资产（"CLI 候选已通过"）。
实测表明它在**他人机器上不能构建**：mathlib 被指到 `C:/Users/18746/Desktop/数竞屠宰场/...`。
所以 P3 的当前位置不是"随时可接手"，而是"先把 mathlib 来源改成可解析的形式"。

**改写 3（P6 的地位）**：第一层把 P6 说成"只用于隔离义务、不缩短到 G0 的路"。这一点仍然成立，
但第五层给出了一个新事实：**在当前证据状态下，P6 是六条路径里唯一"零前置"的**。
这意味着它可以立刻开工，用来产出**可交付的、诚实的中间态**（把假设显式化的下游定理），
而不是等 B1/B3 处理完。它的价值从"隔离义务"升级为"唯一现在就能交东西的路径"。

### 6.3 比对后的路径排序（当前证据状态）

```text
现在可开工：  P6（零前置） →  P2（需 E1 修构建） →  P1 / P5（同需 E1） 
先修再谈：    P3（先修 default target 与绝对路径）
暂不可开工：  P4（等 D4/D7）
```

注意这个排序**不代表数学价值排序**：P1 仍是主线，P6 只是"最容易交东西"。
把两者混淆就是把"可交付性"当成"重要性"，这本身是一种偷换。

---

## 7. 边界

- 本文的 5.0 两条是 `MEASURED`（命令与输出都可复算）；其余仍是设计，未完成任何工件。
- `lake build CoreTransport` 的成功**不代表数学正确**：它只说明源码能编译；公理导出与 `-DwarningAsError` 的逐文件检查仍未做。
- 修好构建不等于数据集成立：`core-log` 的 mathlib 指向改成相对/解析式之前，任何"他人可复现"的说法都不成立。
- 核心 GAP 全部保持 OPEN。
