# 第七轮（我方第二轮探索）：加权账本与陈述锁

日期：2026-10-20（Asia/Shanghai）。分支：`research/round6-bridge`（续第六轮同一工作分支，
仍是 3 个提交之上的新增提交；`main` 与两套既有工程未改动）。**本轮仍不关闭任何 gap，
不证明 Corollary 3.12、不证明 abc、不裁决 Step (v)。**

第六轮（我方第一轮）交付了基域层梯、可容许性障碍与槽位共轭。本轮把其中两条线合成一条
**加权账本**，并补一个新的验收工具**陈述锁**。选择这两项的理由：

- 数学上，pilot 数据真正会用到的是**带权的**总量，而不是我上一轮算的无权总量；
- 工程上，第六轮暴露出一个真实缺口：验证器只锁源码哈希，锁不住"定理的含义"。

## 一、加权账本：`IUTBridge/WeightedLedger.lean`（14 条）

对实际 `Q_p` 元组 `x`、整数权重向量 `w`，定义

```text
vprofile x j := (x j).valuation          -- 逐槽估值
weightedLedger w x := Σ_j w j * vprofile x j   -- 加权估值账本
```

主要结论：

| 定理 | 内容 |
|---|---|
| `vprofile_relabel` / `vprofile_slotwise` | 重标置换估值剖面；逐槽标量作用把剖面平移该标量的估值 |
| `weightedLedger_relabel` | 重标后的账本 = 原账本**按置换后的权重**读取 |
| `weightedLedger_slotwise` | 账本在逐槽标量作用下**恰**平移 `Σ_j w_j · v(a_j)`，没有其他项 |
| `weightedLedger_uniform` | 均匀缩放 `p^k` 平移 `k · Σ_j w_j` |
| **`weightedLedger_invariant_iff`** | **加权账本对所有元组 `σ`-不变 ⟺ 权重向量 `σ`-不变** |
| `totalLedger_relabel` | 无权总量（`w ≡ 1`）对**任意**标号作用不变 |
| `weightedLedger_invariant_of_symm` | 权重对称 ⇒ 账本不变（部分对称性可只在权重层判定） |
| `pilotWeights_not_invariant` / `pilotLedger_not_invariant` | pilot 式权重 `(1,1,2,1)` 在 `swap 2↔3` 下不变性失败，并有具体元组见证 |
| `norm_prod_eq_zpow_totalLedger` | `∏_j ‖x_j‖ = p^(−(总账本))`（要求各坐标非零、`w ≡ 1`）：这是指数关系，不是 Arakelov 对数体积 |

这条 `iff` 是本轮最实的结论：**要不要担心标号作用，可以完全在权重向量上判定，不必挑元组**。
它把第六轮"槽位共轭"（族的不变性）与层梯（估值的精确平移）合成为一条可比对的判据：pilot 式
非均匀权重在 `2↔3` 交换下**必然**破坏加权总量，而均匀权重永不破坏。

## 二、新工具：陈述锁 `tools/statement_lock.py`

**动机（第六轮暴露的真实缺口）**：每套工程的验证器锁定的是 `input_sha256`，即**文件字节**。
它区分不了"文件改了"与"这条定理的命题改了"。设想后续轮次把某条定理悄悄改弱（或改强）、
重跑验证器、刷新文件哈希——所有门禁仍然是绿的，而下游结论其实换了一个命题。

**做法**：对三套工程里**每一条 theorem**（不限于目录内），锁定其

- 规范化后的 elaborated statement 的 SHA-256（规范化规则与 `tools/bridge.py` 共用，避免两个
  审计器各自漂移）；
- 公理集（防止某条定理悄悄多出一个非标准公理）。

默认模式拒绝三类漂移：statement 变化、定理消失、公理集变化；新增只报告不阻断。
`--update --note "..."` 才允许重新锁定，并在锁文件里追加一条历史记录，说明为什么改。

**规模**：`main` 73 + `local` 31 + `bridge` 84 = **188 条 theorem** 被锁定。

### 负向测试（三层，逐层加强）

| 篡改 | 期望 | 实测 |
|---|---|---|
| 改锁文件里一条 statement 哈希 | 失败 | `FAIL changed bridge:…rectangular_iff_product (statement)` |
| 往锁里塞一条不存在的定理 | 失败 | `FAIL removed bridge:IUTBridge.Ghost.theorem` |
| **把一条真实定理改述（仍为真、验证器全绿）、重跑验证器、再查锁** | 失败 | 验证器 `Zero-diagnostic … 56 theorems` 全绿；锁 `FAIL changed bridge:…composeShift_eq_shift_sum` |

第三条是关键：它证明**新工具补上了既有门禁抓不到的那一类问题**。测试用的改述是把
`composeShift p l = shift p l.sum` 改成 `= shift p (l.sum + 0)`（命题等价、证明通过、
公理不变、假设不变），随后已还原并重新验证。

顺带得到一条实事求是的观察：把 `mem_layer_iff_norm_le` 的 `(-k)` 改写成 `(0 - k)` 时，
下游三条证明立刻失败——**即使等价改写也会沿依赖传播**，所以"悄悄改弱"在 Lean 里通常表现为
编译失败；真正危险的是**新增一条更弱的定理再假装它替代了旧的**，而那正是陈述锁 + 合同审计
（`BR-*` 端点必须存在且 statement 未变）能拦住的。

## 三、合同与验收状态

- 合同总数 **8**（新增 `BR-08`：抽象整数加权比较 ↔ 实际加权估值账本，`proof_transfer: false`）。
- 目录定理 **56** 条（`ScaleLedger` 21 / `Admissibility` 12 / `Slots` 9 / `WeightedLedger` 14）。
- `bridge` 工程导出 105 个常量（84 theorem + 21 定义）；公理分布：73 条用
  `Classical.choice`，5 条零公理，4 条仅 `Quot.sound`+`propext`，2 条仅 `propext`，
  全部在 `propext / Classical.choice / Quot.sound` 白名单内。
- `lake build --wfail` 零 warning；四份源码零诊断；入口 112 条 information、0 error / 0 warning；
  假设审计 56 条全部与内核一致。

**准入仍是 0 条**（`Admitted=0, pending=56`）：仓库规则要求实际编辑器观察 + receipt。
我没有伪造，也不会把 CLI 全绿写成通过验收。

## 四、未做与未声称

- 未构造任何 IUT 对象；pilot 权重 `(1,1,2,1)` 只是**手选的**非均匀例子，**不**声称它就是
  真实 pilot 的权重向量（合同 `BR-08` 的 `notes` 已写明这一点）。
- p-adic 对数在本 Mathlib pin 上仍不存在（第六轮已给出编译级证据），RI-06 的 log-image
  身份仍未形式化（本 pin 无可直接调用的 log 接口）；本轮没有绕过它。
- 加权账本是基域 `Q_p` 的整数记账，不涉及 tensor normalization、holomorphic hull、
  全局误差预算，也不构成对 Step (v) 异议的支持或反驳。
- 未建立新颖性主张。

## 五、交接给 Astra

1. 本轮新增的 14 条定理仍需编辑器观察（`bridge/` 的四份文件 + `EditorCheck.lean` 112 条
   information）；补 `vscode-observation-round7.txt` 与 receipt 后重跑
   `python bridge/tools/verify.py` 才会准入。
2. 建议把 `python tools/statement_lock.py` 加进每轮收尾流程；它不依赖 Lean 重编译，只读
   三套工程已生成的导出，几秒即可跑完。
3. 复核 `BR-08`：确认它只是"抽象加权比较 ↔ 基域加权账本"的对应审计，不构成跨工具链证明转移；
   并确认 `notes` 里关于 pilot 权重**非真实数据**的声明没有被下游误读。

## 复现

```powershell
cd bridge; lake build; python tools/verify.py; cd ..
python tools/bridge.py
python tools/statement_lock.py
```
