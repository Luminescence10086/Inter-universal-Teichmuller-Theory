# T008 — 第 3 轮独立审查（Reviewer A：证据与门禁）

- 审查对象：`delegated/2026-10-24/T008/`（已落 `delivery.json`）
- 审查时刻：2026-10-24 13:38–13:47（本机）
- 审查方式：只读；**12/12 哈希自行重算**；Arrow Table 逐条回到源码核对；不采信 `check_delivery.py` 的 `PACKAGE_COMPLETE`

---

## 0. 结论摘要

| 门禁 | 判定 |
|---|---|
| 1 `delivery.json` 各 SHA 与磁盘一致 | **PASS**（12/12 全中，我逐条重算） |
| 2 runs 的 argv 显式 / 无空转 | **PASS**（3 条 argv 均点名具体文件；`nothing to build` 零命中） |
| 3 退出码可反推 / stdout·stderr 完整 | **PASS**（stdout 29752 B 非空、stderr 0 B 且语义为"确无输出"，见 §3） |
| 4 sorry/axiom/白名单 | **PASS**（0 活跃 sorry；11 条 axioms 全在白名单） |
| 5 状态标签未抬高 | **PASS**（`RESEARCH_ONLY`；`editor.performed=false`；`not_claimed` 明确排除 fact-tree 准入） |
| 6 越界写入 | **PASS**（`candidates/core-kummer/**` 与 `fact-tree/**` 在任务窗口内零改动） |

**总判定：`PASS_WITH_FINDINGS`** —— 证据门禁全过，但 §4 的「18 条已构造」有 **3 条在我这把尺子下应降档**，其中 **A14/A15 取决于是否承认"引理委托"**。

---

## 1. 12 个 artifacts 的 SHA——逐条重算

自行 `Get-FileHash -Algorithm SHA256` 重算，与 `delivery.json` 声明逐条比对：

```
MATCH = 12 / 12      MISMATCH = 0      MISSING = 0
```

| 文件 | 字节 | 角色 |
|---|---|---|
| `SUMMARY.md` | 3489 | summary |
| `ARROW-TABLE.md` | 15792 | arrow_table |
| `GAP.md` | 4506 | gap |
| `replay.ps1` | 4903 | replay |
| `probe/T008Probe.lean` | 4167 | probe_source |
| `logs/probe.stdout.log` | 29752 | stdout |
| `logs/probe.stderr.log` | 0 | stderr（`e3b0c442…` = 空文件标准哈希） |
| `logs/replay.stdout.log` | 29752 | stdout |
| `logs/replay.stderr.log` | 0 | stderr |
| `logs/replay.console.log` | 5160 | replay_console |
| `logs/attempt1.stdout.log` | 22944 | discarded_attempt_log |
| `logs/attempt1.stderr.log` | 0 | discarded_attempt_log |

**附加核验（声明方没做，我补做）**：`logs/probe.stdout.log` 与 `logs/replay.stdout.log` 声明 **同一 SHA `29166b5f…`**，即两份 29752 B 文件**逐字节相同**——这验证了 run 2 的 note「its stdout is byte-identical to logs/probe.stdout.log」。**这不是复制粘贴的懈怠，而是 run 2 复用同一 probe 的合理结果**，且 delta 为 0 反而是干净信号。

---

## 2. 三条 runs —— argv / 目标 / 空转

### run 1（kind=lean，exit 0，49.06 s）
```
argv: ["lake","env","lean","-DwarningAsError=true",
       "D:\\…\\delegated\\2026-10-24\\T008\\probe\\T008Probe.lean"]
cwd : D:\\…\\candidates\\core-kummer
```
- **argv 点名具体文件 ✅**——绝对路径直指 probe 源，**不是** `lake build` 无参、**不是** `lake build @/all`、无 `--no-build`。故不可能出现 `nothing to build` 伪装。
- `inputs[0]` 声明的 `probe/T008Probe.lean` SHA = `9035c0b9…`，我实算**一致**。
- **空转短语扫描**：对 T008 全目录 `*.log/*.md/*.json` grep `nothing to build` / `no targets specified` / `Build completed successfully` → **ZERO HITS**。

### run 2（kind=replay，exit 0，48.92 s）
```
argv: ["powershell.exe","-NoProfile","-ExecutionPolicy","Bypass","-File",
       "D:\\…\\T008\\replay.ps1"]
```
- 是**端到端重跑交付脚本**，argv 点名脚本本身；`console` 另存 `logs/replay.console.log`（5160 B，非空）——**外层 shell 的输出被保留**，这正是我第 2 轮要求 v2 补的那一类东西。
- stdout 与 run 1 逐字节相同（见 §1），**两run 互证**，且 exit 均为 0。

### run 3（kind=discarded_attempt，**exit 1**，52.85 s）
- **这条是加分项，不是缺陷。** 任务主动保留了一次**失败**运行（`attempt1.stdout.log` 22944 B），并明确写
  `note: "PRESERVED AS A NEGATIVE RECORD, NOT AS EVIDENCE … Do not use this run for any claim."`
- `inputs: []` 且注明「attempt-1 源文件已被替换、未保留，故无法诚实绑定 SHA」。**这是正确的诚实处置**——宁可留空也不编一个 SHA。
- 我核了 `attempt1.stdout.log` 确实是 attempt1 的现场（含 `letI` 相关失败迹象），与 probe 源 L8–L12 注释所述「elaborator 把局部 def 的值替换成 `sorry` 并丢掉 `hk/hkres`」一致。
- **注意**：`delivery.json` 把 exit 1 的 run 与两条 exit 0 的 run 并列，**但没有把 exit 1 混算成通过**（`note` 明确排除）。这是正确的。

**三条 runs 的退出码可反推性**：run 1/2 stdout 为 29752 B 的真 elaborator 输出、stderr 0 B；若退出码非 0，stdout 里必有 `error`。我逐行扫 `\berror\b` → **0 行**；`\bwarning\b` → **0 行**。故 `exit_code: 0` 与 stdout/stderr **互相印证，不矛盾**。

---

## 3. probe 的四项声明——逐条核

对 `logs/probe.stdout.log`（29752 B、203 物理行）逐行解析：

| 声明 | 我的实测 | 判 |
|---|---|---|
| `-DwarningAsError=true` 下 **exit 0** | argv 含该 flag；exit 0；stdout 无 error | ✅ |
| **零 error** | 含 `\berror\b` 的行 = **0** | ✅ |
| **零 warning** | 含 `\bwarning\b` 的行 = **0** | ✅ |
| **零 sorry** | 源文件 `\bsorry\b\|\badmit\b\|^\s*axiom\s` 命中 **2 处，均在 L1–L20 的 `/- … -/` 块注释内**（L9、L12 是叙述 attempt1 失败的文字）；**无活跃证明义务** | ✅ |
| **23 条 `#check`** | 源文件 `^\s*#check` = **23**；stdout `^@` 行 = **18** | ⚠ 见下 |
| **11 条 `#print axioms`** | 源文件 = **11**；stdout `depends on axioms` = **11** | ✅ |
| **11 条 axioms 全白名单** | `propext=11, Classical.choice=10, Quot.sound=10`；**无 `sorryAx`、无第四种公理** | ✅ |

**关于 `@` 行 18 vs `#check` 23**：这一点**不是缺陷**，但交付方的 note 措辞会造成误读。
`logs/probe.stdout.log` 里 `@` 开头的行只有 18 条，因为**有 5 个 `#check` 的目标是已定义的常数/结构体字段，Lean 打印时不带 `@`**（如 `ValuationSubring.decompositionSubgroup`、`ContH1.map` 等以普通常数形式打印）。23 条 `#check` 全部有输出，只是 **18 条以 `@` 前缀、5 条不带**。我逐条对过 23 个目标名，**全部在 stdout 中出现**。
⇒ **23/23 成立**，但 `delivery.json` 的 note「23 #check lines … all emitted」字面上是对的，若有人按 `@` 计数会误判为 18。**建议 note 补一句"其中 18 条以 `@` 前缀打印"。**

**11 条 axioms 的名单**（与源码逐一对应）：
`decompositionMap` / `muAction` / `reduceMu` / `ker_decompositionMap` / `continuous_decompositionMap` / `reduceMu_smul` / `decompositionMap_surjective` / `decomposition_kummer` / `decomposition_kummerValue` / `CoreCohomologyReflection.*`（经 ReducedComparison 2 条）。

---

## 4. **关键项**：18 条「已构造」里有没有把 `rfl` / 取字段冒充实质构造？

我按「**该箭头是否承载超出其输入的数据**」这一把尺子逐条审。**结论：有 3 条应降档，另有 2 条高度依赖"引理委托"是否算数。**

### 4.1 应降档的 3 条

**A03（`decompositionMap_apply`，ARROW-TABLE 自己已标 `rfl`）**
- 源码 `Decomposition.lean:85-86`：`theorem decompositionMap_apply … := rfl`。**它是真 `rfl`，一个字都没错。**
- 但 ARROW-TABLE 把它列入「已构造 18 条」并按 §3 计数，**而它不含任何数学内容**——它是 `decompositionMap` 的**定义展开**。
- 判定：**不应计入"已构造"的实质内容**。交付方已在备注写 `rfl`（诚实），但**计数口径把定义展开算成了构造**，属口径偏宽。**建议降为 A02 的注记（A02.1），不计入 constructed 计数。**

**A01（`D_A ↪ G`，`Subgroup.subtype`）**
- 源码：`(A.decompositionSubgroup F).subtype`，就是 Mathlib `Subgroup.subtype`。
- `ARROW-TABLE §1.1` 自己写明「是**包含**，不是商映射」。**但它仍然是"从库中取出一个已有映射"**，本任务没有构造任何东西。
- 判定：**它是对 Mathlib 现成构造的引用，不是本任务的构造**。若「已构造」的定义是"该箭头的 Lean 项已被 elaborator 打印出来"，则成立；若是"本任务造出了箭头"，则**不成立**。**这一条应明确标注归属（Mathlib 侧）。**

**A09（`specMu` 的一般引擎）**
- 源码 `Decomposition.lean:150`：`reduceMu … := specMu n A.toSubring (mem_of_pow_mem_toSubring …) (residue A)`。
- 即 **A09 就是 A08 的展开式**，A08 是 A09 的一个实例。两者**不是两条独立箭头，是同一个 def 的两种写法**。
- 判定：**A08/A09 应合并为一条**，否则 constructed 计数虚高 1 条。ARROW-TABLE §1.4 其实已经把关系写对了（"它是 `specMu` 的一个实例"），**但 §3 的计数没反映这一点**。

### 4.2 高度依赖「引理委托」的 2 条

**A14（`decomposition_kummer`，方块交换）——这是全表最重要的一条，也是最需要说清的一条。**
- 源码 `Decomposition.lean:180-192`：证明体**只有 3 行**
  ```
  letI := muAction F A hk hkres n
  map_kummer_eq_map_kummer n (A.decompositionSubgroup F).subtype (decompositionMap …)
    (fun _ _ => rfl) A.toSubring (mem_of_pow_mem_toSubring A n hn) (smul_mem_toSubring F A)
    (residue A) (residue_smul_eq F A hk hkres) continuous_subtype_val
    (continuous_decompositionMap F A hk hkres) f a hf hf' hfa
  ```
- 真正的数学在 `Specialization.lean:147-188` 的通用引擎 `map_kummer_eq_map_kummer`（42 行实质计算：取 `α := kummerRoot`、证 `α ∈ B`、`α⁻¹ ∈ B`、构造 `β := Units.map ψ (unitOfMem …)`、逐点 `funext d` 后 `Mu.ext`/`Units.ext` 落到 `cocyclesMap_apply` 与 `coe_val_specMu`）。
- **我的判定**：**A14 成立为「已构造」，但它的实质内容 90% 在 Specialization.lean，不在 A14 自己的证明体里。** 这不是造假——**引理委托是正常证明方式**；但台账若让人以为「方块交换性是在 A14 里证出来的」就是误导。
- **ARROW-TABLE 已部分披露**（§0 提到 `map_kummer_eq_map_kummer`），但**没有说明 A14 的证明体只有 3 行、实质在引擎里**。建议补一行「本箭头为引擎定理的实例化，实质证明见 `Specialization.lean:147-188`」。

**A15（`decomposition_kummerValue`）** —— 同上，委托给 `map_kummer_eq_map_kummerValue`（`Specialization.lean:231`）。同理成立但需披露。

### 4.3 明确**不**该降档的（我核对后认可）

- **A07 `muAction`**：`:= MulDistribMulAction.compHom _ (decompositionMap …)`（L139-141）。**是 `compHom` 的直接应用，属"取出字段式"构造**……但 `compHom` 本身就产生一个**新的** `MulDistribMulAction` 实例，且 ARROW-TABLE §1.3 已明确写出「类型层面它不携带任何超出 `decompositionMap` 的数据」。**披露充分，保留「已构造」。**
- **A10 `reduceMu_smul`**：证明体调 `specMu_smul`，但陈述里的 `letI := muAction …`（L165）与消费侧必须复现同一 `letI`，**这是实质的接口约束**，保留。
- **A05 `ker_decompositionMap`**：证明是 `ext σ` + 双向 `DFunLike.congr_fun`，**几乎是定义对齐**。Mathlib `inertiaSubgroup` 定义即 `MonoidHom.ker (MulSemiringAction.toRingAut …)`（`RamificationGroup.lean:50-52`），与本定理右边同构。**这条实质内容少，但因两侧构造不同源，"对齐"本身有价值**——我判**保留，但建议在备注里写明"证明为定义对齐，非新定理"**。
- **A18 `pullback_injective`**：`ReducedComparison.lean:16-20` 直接调 `CoreCohomologyReflection.map_injective`（`CohomologyReflection.lean:15-32`，实质证明：`mk_surjective` 两次、`mk_eq_mk_iff`、用 `hsurj` 取原像、`e.injective`）。**引理委托，且被委托方是实质证明 → 保留。**

### 4.4 constructed 计数的净结论

- 交付方声明 **18 条**。
- 按我的尺子：**A03 应降为注记（−1）**、**A09 应与 A08 合并（−1）**、**A01 应标注为 Mathlib 引用（不降档但需归属）**。
- 修正后口径：**实质构造 16 条**（A01 记为外部引用）；若严格按「本任务构造」计，则更少。
- **但请注意**：这不是"造假"。ARROW-TABLE 对 A03 的 `rfl`、A01 的"包含非商"、A09 的"specMu 实例"**都已经诚实写出**。**问题只在 §3 的计数口径把注记也算进了 18**。

---

## 5. A21 的 olean 缺失——**核为真**

- 实测 `candidates/core-kummer/.lake/build/lib/lean/Boundary/` 下 8 个 olean：
  `AnchoredComparison`、`DiscreteValuation`、`FinitePlace`、`Frontier`、`PrecisionLoss`、`ProjectiveComparison`、`ReducedComparison`、`ThetaGermTransport`。
  **确实没有 `DecompositionBridge.olean`。**
- 递归搜索 `.lake` 下任何 `*DecompositionBridge*` → **空**。
- 而**源文件存在**：`Boundary/DecompositionBridge.lean`，4321 B，mtime 10/24 10:24:32。
- ⇒ **A21 的「无 olean、无法 elaborator 核验、故不记已构造」完全属实，且处置正确**（按 PROTOCOL「代理自报 ≠ 已验证」）。
- `delivery.json` 的 `upstream_inputs` 里对 `DecompositionBridge.lean` 标 `matches_baseline: true` 但备注 `NOT verifiable by this task: no …olean exists`——**这是诚实的，没有把"文件哈希对得上"偷换成"内容已验证"**。
- **一处小建议**：源文件存在但未建构，说明该文件**可能有编译错误**（或只是从未被 `lake build` 目标覆盖）。建议后续任务把它列入"待建构清单"，而不是长期挂 UNDECIDABLE。

---

## 6. `muAction` 的 `letI` 陷阱——**有源码依据，非推测**

交付方断言：「`Mu n κ` 本身已由 `Basic.lean:86-91` 对 `Gal(κ/k)` 给出一个 `MulDistribMulAction` 实例。若忘记 `letI := muAction …`，右侧 `σ •` 会落到**另一个**作用上，语句变成不同命题。」

逐条核：

1. **竞争实例真实存在 ✅** —— `ContinuousKummerTheory/Kummer/Basic.lean:86-91`：
   ```lean
   instance : MulDistribMulAction Gal(Ω/K) (Mu n Ω) where
     smul g ζ := mk (g • val ζ) (…)
   ```
   这是 `Gal(Ω/K)` 在 `Mu n Ω` 上的**全局实例**。
2. **`muAction` 是同型但不同的实例 ✅** —— `Decomposition.lean:139-141`：
   ```lean
   @[implicit_reducible]
   noncomputable def muAction : MulDistribMulAction (A.decompositionSubgroup F) (Mu n (ResidueField A)) :=
     MulDistribMulAction.compHom _ (decompositionMap F A hk hkres)
   ```
   注意它是 **`def` 且带 `@[implicit_reducible]`，不是 `instance`** ——这正是"必须显式 `letI`"的机械原因。
3. **生产代码确实一律 `letI` ✅** —— 我实测 `Decomposition.lean` 的 **L165、L167、L183、L188、L202、L208** 六处，以及 `KummerClass.lean:174` 一处，共 **7 处** `letI := muAction …`。ARROW-TABLE 引的「`:165,183,188,202,208`」**略有出入**（漏了 L167、L202 我数到但 208 也在；实际 L167 与 L183/L188 各一处）。**引用行号不精确，但论断方向正确。**
4. **两个作用在何种意义上不同**：`compHom` 版本是 `d • ζ := (decompositionMap d) • ζ`；全局实例是 `g • ζ := mk (g • val ζ)`。因为 `decompositionMap σ` 逐点等于 `σ • x`（A03，`rfl`），**两者在值上恰好一致**——**但类型级上 `A.decompositionSubgroup F` 与 `Gal(κ/k)` 是两个不同的群，Lean 的实例消解会在不同的 `MulDistribMulAction _ (Mu n _)` 目标上分叉**。
   ⇒ **交付方的"会落到另一个作用上"在类型层面成立；但在数值层面两者一致**。ARROW-TABLE §1.3 写「语句变成不同命题（通常无法关闭，偶有歧义实例时更危险）」——**"变成不同命题"措辞偏重**：实情是**同一命题的不同实例书写**，风险在于 **elaboration 时消解到哪个实例**，而非数学内容不同。

**判定：有源码依据 ✅，非推测；但 §1.3 的后果描述("变成不同命题")应改为"消解到不同实例，导致 elaboration 不一致"。**

---

## 7. 越界写入

- 任务窗口（13:09 起）内 `candidates/core-kummer/**` **零文件**被修改，`fact-tree/**` **零文件**被修改（`LastWriteTime > 13:09` 过滤）。
- `delivery.json` 的 `build_cache_note` 自述「deliberately ran `lake env lean <file>` and NOT `lake build`, so `.lake` was not written」——**与我的实测一致**（`.lake` 下 Boundary olean 最新为 ThetaGermTransport 的 11:58:20，早于 T008 的 13:19 起跑）。
- ⇒ **无越界写入。**

---

## 8. 仍需交付方补的（不影响 PASS，但影响可引用性）

1. **§4.4 的计数口径**：把 A03（`rfl`）降为注记、A08/A09 合并，明确 A01 属 Mathlib 引用 → 修正后 constructed 计数约 **16**。**这是本轮唯一我认为必须改的地方**（因为它直接影响别人引用"18 条已构造"）。
2. **A14/A15 的引理委托披露**：补一行说明实质证明在 `Specialization.lean:147-188 / :231`。
3. **`note` 里"23 #check lines"** 补注「其中 18 条以 `@` 前缀打印」。
4. **§1.3 措辞**："变成不同命题" → "消解到不同实例"。
5. **ARROW-TABLE 引用的 `letI` 行号**（`:165,183,188,202,208` 与实测 7 处）请以实测为准。
6. `editor.performed = false` 已如实声明，**`RESEARCH_ONLY` 未被写成编辑器准入 ✅**——此项无问题，仅记录。
