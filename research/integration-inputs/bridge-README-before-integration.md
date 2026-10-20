# 第三套工程：基域 `Q_p` 的桥接验证

本目录是本仓库的**第三套独立验证工程**，2026-10-20 第六轮新建。它不修改主工程
`IUTAudit`（Lean `4.34.0`，无 Mathlib）与 `local-field`（Lean `4.34.0-rc2`，Mathlib）
中的任何文件，只通过 Lake 路径依赖**读取**后者。

```text
main        Lean 4.34.0      no Mathlib   抽象离散模型（Scale / Transport / Orbit …）
local       Lean 4.34.0-rc2  Mathlib      已验收的真实 Q_p 过滤（Shell / Filtration / ContinuousLinearity）
bridge      Lean 4.34.0-rc2  Mathlib      本目录：基域实现 + 跨工具链接口合同
```

`bridge → local` 是**真实 Lean import**，依赖由内核检查。`main → bridge` **不能**
import（两套工具链的编译产物互不通用），因此那里的对应关系不是证明转移，而是根目录
`bridges/contracts.json` 中登记的**受审计接口合同**，由 `tools/bridge.py` 机械核对：
规范化后的 elaborated statement 文本必须相同、vendored 定义的类型必须相同。

## 内容

- `IUTBridge/ScaleLedger.lean`：实际 `Q_p` 的整数范数层梯 `layer`、缩放自同构
  `shift`，以及两本账：**范数账本乘性**（`‖shift n (shift m x)‖ = p^(-(n+m))·‖x‖`）
  与**估值账本加性**（`(shift n (shift m x)).valuation = n + m + v x`）。列表复合的
  望远镜等于指数求和（路径无关）；层间搬运由带符号指数差 `m-k` 的单一伸缩实现——这是集合恒等式，不是体积或代价估计。
- `IUTBridge/Admissibility.lean`：把主工程的矩形性接口**逐字 vendor**过来，先在一般
  层面证出**图障碍**（联合关系若是图且出现两个不同值，则矩形性必然失败），再在真实
  `Q_p` 上实例化：`LatticeAdmissible p e k` 表示 `e '' ball = layer p k`。两侧边际都全、
  关系是图、因此不矩形；而**正规化子关系**（把层冻结在 `0`）是矩形的。最后一击：
  任何矩形的联合子关系都把层冻结 —— 想要"分别验 Kappa 与 Sigma"就必须先放弃缩放自由度。
- `IUTBridge/Slots.lean`：实际 `Q_p` 元组上的槽位重标 `relabel` 与逐槽标量作用 `slotwise`。
  重标把标量族**共轭**过去，因此逐槽作用与重标交换**当且仅当**标量族在该置换下不变；
  均匀缩放与任意重标交换。这是第五轮"每个 place 的同步条件如何与 label 无关"的玩具版回答：
  同步性 = 标量族的不变性，不是逐 label 的巧合。
- `IUTBridge/WeightedLedger.lean`（第七轮新增）：把上面两条合成**加权估值账本**
  `Σ_j w_j · v(x_j)`。账本在逐槽标量作用下恰平移 `Σ_j w_j·v(a_j)`，范数积是它的指数；
  核心判据是 **`weightedLedger_invariant_iff`：账本对一切元组 `σ`-不变 ⟺ 权重向量
  `σ`-不变**。因此无权总量对任意标号作用不变，而 pilot 式非均匀权重 `(1,1,2,1)` 在
  `swap 2↔3` 下必然失败（有具体元组见证）。权重是手选例子，不是真实 pilot 数据。

## 验收状态：CLI 已核验，**尚未准入**

```powershell
lake build                 # 依赖 ../local-field 与外部 Mathlib（只读复用）
python tools/verify.py     # 零诊断 + 公理白名单 + 假设审计 + 目录核对
```

`tools/verify.py` 与另外两套工程的验证器同构，但多两项检查：

1. **假设审计**（`tools/Binders.lean`）：对每个目录定理机械剥出*语法* forall 望远镜，
   任何显式、非类型类的 `Prop` 绑定都必须先在 `tools/catalog.json` 的 `hypotheses`
   里申报。悄悄多出一个前提的定理会直接验证失败。剥离**不做 reduction**，
   否则 `¬ P` 会被展开成 `P → False`，把否命题误算成前提。
2. **依赖身份**：记录 `../local-field` 证明源码与配置的哈希，桥接结论只能对
   核对过的依赖成立。

当前输出：`Zero-diagnostic source checks passed; hypotheses audited for 56 theorems.
Admitted=0, pending=56, edges=0.`

`Admitted=0` 是**如实状态而非失败**：仓库的准入规则要求实际编辑器观察（`No goals` +
入口零 error/零 warning）并绑定 receipt。本工程还没有这份 receipt，因此
`fact-tree/facts.json` 为空、56 条全部标记 `cli_verified_awaiting_editor`。
CLI 全绿是必要条件，不是准入凭据。

与本工程配套的两个跨工程工具在仓库根目录：`tools/bridge.py`（8 条跨工具链合同的接口审计）
与 `tools/statement_lock.py`（锁定三套工程全部 188 条 theorem 的命题与公理集，防止后续轮次
悄悄改弱已验收的定理）。

## 已知受阻路径：p-adic 对数

RI-06 真正缺的是 `log_p(O^×)` 的像身份。本 pin 的 Mathlib **没有** p-adic 对数：
`#check @Padic.log / @Padic.exp / @Padic.logP / @Padic.pow / @Padic.LubinTate` 全部
`unknownIdentifier`，`Mathlib/NumberTheory/Padics/` 的 16 个源文件里没有对数模块，
全仓 grep `Padic\.log|padicLog|pAdicLog` 零命中。因此 log-image 类桥接必须先自建
`log_p`（含收敛域与同态性），本轮不把它伪装成"再加一条条件式定理"。

## 与外部依赖的关系

- Lean `leanprover/lean4:v4.34.0-rc2`；Mathlib commit
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`（路径见 `lakefile.toml`，实测该 checkout 无改动）。
- `lake-manifest.json` 全量固定为 `path` 类型，避免 Lake 联网解析（本机 git 取不到 GitHub 凭证）。
- 本工程**不**声称实现 IUT 对象：没有 Θ-link、Ism 元素、Kummer 表示、seed 区域成员资格、
  log 像身份、holomorphic hull 或 Arakelov 体积；对 Corollary 3.12 与 abc 不下任何结论。
