# 第六轮：基域桥接工程与跨工具链合同审计

日期：2026-10-20（Asia/Shanghai）。分支：`research/round6-bridge`（基于第五轮结束状态的
本地快照 `main`，**未并入**，等待 Astra 核验）。前置状态：主工程 38 节点 / 14 边、
局部域 24 节点 / 31 边、`GAP.md` 六项与 realization 台账八项全部 open。

本轮目标是用户指定的方向：**研发新工具，或在两套理论之间搭桥**，且结论必须经 Lean
与编辑器检验。本轮**没有**关闭任何 gap，也**没有**证明 Corollary 3.12 或 abc。

## 为什么新建第三套工程

本轮需要在 `Q_p` 上真正使用 `LocalFieldAudit.Filtration` 的结论，又需要引用主工程
`IUTAudit.Scale` 与 `IUTAudit.Transport` 的抽象接口。把新定理直接追加进任一既有工程
都会改变它的 `input_sha256` 快照，使第五轮的 `vscode-receipt.json` 立刻失效、既有
节点集体降级为 pending——那就是污染。因此新建 `bridge/`：Lean `4.34.0-rc2` + Mathlib
`85e3a25e…`，以 Lake 路径依赖**只读**复用 `../local-field`。

实测未污染：`local-field/.lake/build/lib/lean` 下 20 个产物（olean/ilean/trace）在本轮
前后 SHA-256 **逐一相同**；本轮 git 变更为纯新增，未修改两套工程的任何被追踪文件。

## 两条边，强度不同

```text
main   --(合同：受审计，非证明转移)-->  bridge   <--(真实 import：内核检查)-- local
```

- `bridge → local-field`：真正的 `import LocalFieldAudit.Filtration`，由内核检查。
- `main → bridge`：**不可能 import**（Lean `4.34.0` 与 `4.34.0-rc2` 的 olean 互不通用）。
  因此 `IUTAudit.Transport` 的矩形性接口以**逐字 vendor**方式复制到 `Admissibility.lean`，
  两者的对应关系由 `tools/bridge.py` 机械核对，并显式记录 `proof_transfer: false`。
  不把"文本相同"说成"证明转移"，是本轮工具设计的底线。

## 数学内容（42 条目录定理，三个模块）

### `IUTBridge/ScaleLedger.lean`（21 条）

实际 `Q_p` 的整数范数层梯 `layer p k := p^k • ball`（`k` 越大球越小），缩放自同构
`shift p n := ×p^n`。核心是把抽象离散标度模型的两本账在真实算术上分开算清：

| 定理 | 内容 |
|---|---|
| `mem_layer_iff_norm_le` | 层的范数刻画，含 0 |
| `mem_layer_iff_le_valuation` | 层 ↔ 估值刻画（显式非零前提） |
| `zero_mem_layer` / `layer_subset_of_le` / `layer_ssubset_of_lt` / `layer_injective` | 梯是严格递增的无限过滤，层由指标唯一决定 |
| `shift_apply` / `shift_comp_apply` / `shift_ne_zero` | 缩放的底层函数、迭代相加、保非零 |
| `norm_shift` / `norm_factor_composition` / `norm_factor_pow` | **范数账本乘性**：复合因子 = 两因子之积 = `p^(-(n+m))` |
| `valuation_shift` / `valuation_ledger_composition` | **估值账本加性**：`v(shift n (shift m x)) = n + m + v x` |
| `layer_image_shift` | `shift n '' layer k = layer (k+n)`：缩放只搬梯，不改梯形 |
| `cost_exact` | **容器加宽代价**：从 `layer k` 到 `layer m` 恰由指数 `m-k` 的单一伸缩实现 |
| `map_one_determines` / `image_ball_eq_layer` / `existsUnique_layer_of_auto` | 自同构由 `e 1` 决定；球像的层索引唯一 = 联合数据是**图** |
| `composeShift_apply` / `composeShift_eq_shift_sum` | 列表复合缩放 = 指数求和（望远镜、路径无关） |

### `IUTBridge/Admissibility.lean`（12 条）

| 定理 | 内容 |
|---|---|
| `rectangular_iff_product` | vendor 主工程等价并**独立重证**（BR-03 的 statement identity） |
| `not_rectangular_of_graph` | **一般图障碍**：图关系只要出现两个不同值就不矩形 |
| `marginals_insufficient_of_graph` | 一般形式：两侧边际存在仍不矩形 |
| `latticeAdmissible_unique` / `latticeAdmissible_attained` / `latticeAdmissible_refl` | 真实 `Q_p` 联合关系的基本结构 |
| `marginals_total` | 两侧边际**全**（每个自同构有层、每个层可达） |
| `latticeAdmissible_not_rectangular` | 实际非矩形：恒等占层 0、`×p` 占层 1 |
| `marginals_do_not_force_joint` | 三合一主结果：边际全 + 非矩形 = 分别验不算联合验 |
| `normalised_isRectangular` / `normalised_sigma_marginal` | 把层冻结在 `0` 的子关系**是**矩形，其边际恰为 `{0}` |
| `rectangular_subrelation_freezes_layer` | **任何**矩形联合子关系都把层冻结：想分别验就得先放弃缩放自由度 |

第四条（冻结定理）是本轮最有用的新命题：它把"反例"升级成"对修补方案的约束"。任何
试图用两个边际检查替代联合 (κ,σ) 检查的补救路线，在基域层梯这一模型里必须先把层钉死；
若原论证依赖缩放自由度，则该替代不成立。**这不裁决 G03 Step (v)**，只是给出该替代路线的
可失败判据。

### `IUTBridge/Slots.lean`（9 条，第二轮尝试产物）

实际 `Q_p` 元组上的两种作用：槽位重标 `relabel`（按置换 `σ`）与逐槽标量作用 `slotwise`
（第 `j` 槽乘 `a j`）。核心结论：**重标把逐槽标量族共轭过去**，因此逐槽作用与重标交换
**当且仅当**标量族在 `σ` 下不变。

| 定理 | 内容 |
|---|---|
| `relabel_injective` / `relabel_trans` | 重标不丢/不重槽位；重标复合反变 |
| `relabel_slotwise` | **投影公式（玩具版）**：`relabel σ (slotwise a x) = slotwise (a ∘ σ⁻¹) (relabel σ x)` |
| `valuation_relabel_slotwise` | 运输后逐槽估值记账（显式非零前提） |
| `slotwise_commutes_of_invariant` | 标量族 `σ`-不变 ⇒ 与重标交换 |
| `slotwise_not_commutes_of_witness` | 存在槽位受不同标量 ⇒ 不交换（常 1 元组作见证） |
| `uniform_scale_commutes` | 单一标量（均匀缩放）与**任意**重标交换 |
| `swap23_fixes_low_slots` / `swap23_exchanges_high_slots` | 具体 `σ=(2 3)`：低槽不动、高槽互换 |

这条把第五轮留下的问题——"每个 place 的同步条件如何与 label 无关"——回答了
**玩具形式**：同步性等价于标量族的 `σ`-不变性，而不是逐 label 的巧合。仍无任何 IUT 对象。

## 第二轮尝试：三条候选路径的成败

| 路径 | 内容 | 结果 |
|---|---|---|
| A | 标度/估值双账本（`ScaleLedger`） | ✅ 成功，21 条 |
| B | 联合可容许性与矩形性（`Admissibility`） | ✅ 成功，12 条 |
| C | 真实 `log_p(O×)` 像身份（RI-06 真正缺的那块） | ❌ **受阻**：本 Mathlib pin 无 p-adic 对数 |
| D | 槽位重标 × 逐槽标量作用（`Slots`） | ✅ 成功，9 条 |

路径 C 的证据是编译级而非文献级：`#check @Padic.log / @Padic.exp / @Padic.logP /
@Padic.pow / @Padic.LubinTate` 全部 `unknownIdentifier`；`Mathlib/NumberTheory/Padics/`
下 16 个源文件（`AddChar`、`Hensel`、`PadicIntegers`、`WithVal` …）无对数模块；全仓
`grep "Padic\.log|padicLog|pAdicLog"` 零命中（`log` 命中均为 `Nat.log` / 实数对数的引理）。
因此 RI-06 的 log-image 身份在当前 pin 上**无法形式化**，必须先实现
`log_p : ℤ_[p]^× → ℚ_[p]`（含收敛域与同态性）。这是一条下一步该先建的基础设施，
而不是再写一条条件式桥接定理。


## 新工具

### 1. `bridge/tools/verify.py` + `tools/Binders.lean`：假设审计

既有两套验证器只审公理与目录，不审**前提个数**。本轮的验证器要求每个目录定理把它
所有"显式、非类型类 `Prop` 绑定"申报在 `catalog.json` 的 `hypotheses` 里。实现要点：
按**语法**剥 forall 望远镜，不 reduction，否则 `¬ P` 会展开成 `P → False`，把否命题
误算成前提（本轮开发中确实踩到，已修正并留证）。

### 2. `tools/bridge.py` + `bridges/contracts.json`：跨工具链合同审计

七条合同（`BR-01`–`BR-07`），每条核对：端点定理真实 elaborated、类型是 theorem、
公理在白名单内、导出未过期（源码哈希比对）；`statement_identity` 类还要求规范化后
的 statement 文本**逐字相同**，并对 vendored 定义比对 elaborated 类型；每条合同
必须申报"未构造哪些 IUT 对象"，申报为空即失败。

### 负向测试（证明这些检查会失败）

| 篡改 | 期望 | 实测 |
|---|---|---|
| 给 `mem_layer_iff_norm_le` 虚报前提 `hx` | 失败 | `hypotheses for …: kernel reports [], catalog declares ['hx']` |
| 把 BR-03 具体端换成 `marginals_do_not_force_joint` | 失败 | `BR-03: statements differ` |
| 篡改后还原 | 通过 | `Contracts checked: 6; failures: 0` |

## 验收状态（如实）

| 项目 | 状态 |
|---|---|
| `lake build`（bridge） | 成功，零 warning（`--wfail`） |
| 三份源码 `lean --json -DwarningAsError=true` | stdout/stderr 为空 |
| 目录定理 | 42 条全部 elaborated；公理 ⊆ `propext` / `Classical.choice` / `Quot.sound`。本工程共 65 条 theorem / 16 个定义，其中 55 条用 `Classical.choice`，5 条零公理，4 条仅 `propext`+`Quot.sound`，1 条仅 `propext` |
| 入口 CLI | `2 × 42 = 84` 条 information，0 error / 0 warning |
| 假设审计 | 42 条全部与内核一致 |
| 合同审计 | 7 条全通过，`proof_transfer: false` |
| **编辑器准入** | **0 条**：尚无实际 VS Code 观察与 receipt，故全部 `cli_verified_awaiting_editor` |

必须说清楚：本轮**没有**取得编辑器验收，因此按仓库规则这些定理**都还不能算已准入**。
我能做的是把机器可核验的部分做到可复现，并给出负向测试；`No goals` 与 UI 零告警
需要 Astra 在真实编辑器里补。

## 交接给 Astra 的清单

1. 在 VS Code 打开 `bridge/`（使用 `4.34.0-rc2`），确认两份源文件末尾证明 `No goals`。
2. 打开 `bridge/tools/EditorCheck.lean`，展开 All Messages 应有 84 条 information、
   状态栏 0 error / 0 warning。
3. 按第五轮格式写 `bridge/verification/vscode-observation-round6.txt`，再生成
   `bridge/verification/vscode-receipt.json`（`schema: 2`，需含 `dependency_sha256`），
   然后重跑 `python bridge/tools/verify.py`，节点方可准入。
4. 决定是否把 `bridge/` 与 `bridges/` 并入 `README.md`、`GAP.md` 与根 `fact-tree/catalogue.md`；
   本轮**没有**改动这些权威文件，以免在核验前改写第五轮结论。
5. 复核 BR-03：确认它只是接口对应审计，不构成跨工具链证明转移。

## 复现

```powershell
cd bridge
lake build
python tools/verify.py
cd ..
python tools/bridge.py
```

## 未做与未声称

- 未构造任何 IUT 对象（Ism / Kummer / packet / seed / region / hull / log-volume）。
- 未证明 Corollary 3.12、未证明 abc、未判定 Step (v) 异议对错。
- 未建立新颖性主张；`cost_exact`、图障碍、冻结定理都是基域层梯上的初等事实，
  它们的价值在于**约束修补路线**与**可机器复核**，不在于学理首次性。
- 无跨工具链证明转移：`main` 的抽象结论不会自动在新的工具链里成立，只有被
  vendor + 独立重证的部分（`rectangular_iff_product`）才真正存在两份证明。

## 环境与网络

- Lean `4.34.0`（main）与 `4.34.0-rc2`（local / bridge）；Mathlib
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`。
- 用户提供的远端 `https://github.com/Luminescence10086/Inter-universal-Teichmuller-Theory`
  已登记为 `origin`，但本沙箱内 git 取不到 TLS 凭证
  （`schannel: AcquireCredentialsHandle failed: SEC_E_NO_CREDENTIALS`），`git ls-remote`
  以 128 退出，因此本轮**未能推送**；分支仅存在于本地。
