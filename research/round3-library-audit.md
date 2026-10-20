# 第三轮：局部线性代数与 Lean 库接口审计

日期：2026-10-16（Asia/Shanghai）。范围：只读检查已知 Lean 项目的 Mathlib、`.elan` 工具链及官方在线文档/公开 LANA 源码。没有扫描整个用户目录，没有执行外部仓库脚本，没有重装环境，没有改生产 Lean 或验证器。**本报告的源码定位及候选桥接均不是已完成 VS Code 验收的 fact-tree 节点。**

## 1. 本机可用版本与编译产物

找到真实 Mathlib 安装：

```text
C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib
git HEAD = 85e3a25e006c35636f0e53b0e9296caca2685bc0
lean-toolchain = leanprover/lean4:v4.34.0-rc2
git status --short --untracked-files=no = 空
```

匹配 Lean 二进制：

```text
C:/Users/18746/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean.exe
Lean 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d
```

本次确实执行了该二进制的 `--version`。Mathlib 的 `Map.olean`、`Pointwise.olean`、`PadicIntegers.olean` 及根 `Mathlib.olean` 均存在于 `.lake/build/lib/lean/`；根产物为 773496 字节。这确认有与其声明工具链配套的现成产物，尚不等于已重建或逐依赖审计这些产物。

`.elan/known-projects` 还登记 `Desktop/Lean 4/test_project`，它也有 Mathlib 包；数竞项目另有 `mathlib_old`，本次所读版本同为上述 commit/rc2，没有借名称猜测其版本。未修改任何这些项目。

**接入建议**：用独立子工程和匹配 rc2 二进制、显式 `LEAN_PATH` 读取已安装产物；不要用主项目 4.34.0 正式版直接读 rc2 `.olean`。需要同时列入 Mathlib 依赖包的 `.lake/build/lib/lean`，不能只列根 Mathlib 目录。若改用 path dependency，也只在独立子工程操作，不改数竞项目配置。实际 proof 检查和 VS Code 验收由后续独立工程保存日志。

## 2. 已固定的只读源码缓存

`research/round3-source-cache/manifest.json` 记录六份原样源码、commit、完整上游 URL 和 SHA256；总计 135359 字节，仅供审计，没有导入生产项目：

- `Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean`
- `Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `Mathlib/Algebra/Module/Submodule/Map.lean`
- `Mathlib/Algebra/Module/Submodule/Pointwise.lean`
- `Mathlib/NumberTheory/Padics/PadicIntegers.lean`
- `Mathlib/NumberTheory/LocalField/Basic.lean`

对应固定版本源码入口：[Mathlib commit 85e3a25](https://github.com/leanprover-community/mathlib4/tree/85e3a25e006c35636f0e53b0e9296caca2685bc0)。在线滚动文档只用于交叉定位，不取代此本机固定字节版本。

## 3. 可直接复用的代数接口及完整前提

### 3.1 最短路径：`Set.image_smul_comm`

固定源码 `Algebra/Group/Pointwise/Set/Scalar.lean:315–316`：

```lean
lemma Set.image_smul_comm
    [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s
```

只要求两个标量作用及显式交换条件，没有局部域、拓扑、有限维或估值前提。集合缩放需 `open scoped Pointwise`。对于真正的线性映射，交换条件可由 `LinearMap.map_smul` 提供；若还知道 `f '' L = L`，候选推导是 `f '' (a • L) = a • L`。这避免先把格误建模为基域子空间。

固定源码 `LinearMap/Defs.lean:336` 的普通线性版本：

```lean
-- [Semiring R], [AddCommMonoid M], [AddCommMonoid M₂],
-- [Module R M], [Module R M₂]
protected theorem LinearMap.map_smul
    (f : M →ₗ[R] M₂) (c : R) (x : M) : f (c • x) = c • f x
```

`LinearMapClass.map_smul` 还适用于带相应实例的 `LinearEquiv`。若线性只针对 `ℤ_[p]`，它直接给出非负 n 的 `p^n` 交换；要处理所有 `n:ℤ` 的负幂，须在 `ℚ_[p]` 向量空间上使用 `ℚ_[p]` 线性映射，或先独立证明从格上的 `ℤ_[p]` 线性同构延拓到分式空间。后者不是本报告已完成的实例。

### 3.2 真正的格应是整数环子模

可使用 `L : Submodule ℤ_[p] M`，其中 `M` 同时是 `ℚ_[p]` 向量空间；若要求“格”，还应补有限生成和张成全空间等条件。仅对子模缩放的代数恒等式不需要这些格条件。

固定源码 `Submodule/Pointwise.lean` 的相关接口：

| 接口 | 源码行 | 前提与用途 |
| --- | --- | --- |
| `Submodule.pointwise_smul_def` | 198 | `[Semiring R] [AddCommMonoid M] [Module R M] [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]`；把 `a • L` 实现为标量映射的 `Submodule.map` |
| `Submodule.coe_pointwise_smul` | 202 | 同上；子模缩放的集合载体就是集合缩放 |
| `Submodule.mem_smul_pointwise_iff_exists` | 215 | 同上；`m ∈ a • L ↔ ∃ b∈L, a•b=m` |
| `Submodule.smul_mem_pointwise_smul` | 219 | 同上；原成员经标量作用进入缩放子模 |

要说基域标量 `α=ℚ_[p]` 作用在 `R=ℤ_[p]` 子模上，必须有相容的作用与 `SMulCommClass`；需要根据实际实例验证 elaboration，不能把所需类型类全部默认为自动可得。

`Submodule.mem_map_equiv`（`Map.lean:556` 附近）提供普通同环标量情形的：

```lean
-- [Semiring R], [AddCommMonoid M], [AddCommMonoid M₂],
-- [Module R M], [Module R M₂]
-- e : M ≃ₗ[R] M₂, L : Submodule R M, x : M₂
x ∈ L.map e.toLinearMap ↔ e.symm x ∈ L
```

更一般源码允许带互逆 ring hom 的半线性同构。上述具体化足够处理普通线性格。`map_equiv_eq_comap_symm`、`map_symm_eq_iff` 能把同构正向/逆向保持关系相互转换；**不可仅从 `e '' L ⊆ L` 推出 `e '' L = L`**。

特别警告：`Submodule.map_smul` / `map_smul'`（`Map.lean:514,523`）描述的是以同一个半域 K 为标量的 `K` 子空间，结论如 `p.map(a • f)=p.map f`（a≠0）。这不能当作 `p^n` 整数格缩小的定理；非零 K 标量对 K 子空间本来就不改变它。[官方 Submodule.Map 文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Map.html)

## 4. 已有真正 p 进对象与估值接口

固定源码中 `PadicInt p = {x : ℚ_[p] // ‖x‖≤1}`，配有真正 p 进完备化及 DVR 结构，绝非任意实数数组。通常参数要求 `p:ℕ`、`[Fact p.Prime]`。可定位的接口：

```lean
-- x : ℤ_[p], hx : x ≠ 0, n : ℕ
PadicInt.mem_span_pow_iff_le_valuation :
  x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔ n ≤ x.valuation

-- x : ℤ_[p], n : ℕ；这个版本容纳 x=0
PadicInt.norm_le_pow_iff_mem_span_pow :
  ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔
    x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p])

-- x : ℤ_[p], hx : x ≠ 0, n : ℕ
PadicInt.norm_le_pow_iff_le_valuation :
  ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ n ≤ x.valuation

-- c : ℤ_[p], hc : c ≠ 0, n : ℕ
PadicInt.valuation_p_pow_mul :
  ((p : ℤ_[p]) ^ n * c).valuation = n + c.valuation
```

固定行号分别为 457、470、452、349；这些是从本机源码读到的声明，不是在本工程中重检得到的验收证书。[官方 PadicIntegers 文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicIntegers.html)

**零点约定必须注意**：这里 `PadicInt.valuation 0=0`（Nat 值），`Padic.valuation 0=0`（Int 值），不是数学扩展估值中的 +∞。因此若使用 finite-valued `valuation` 写严格层，相关乘法、范数/估值等价常有非零前提。可以用含零的 norm-ball / multiplicative valuation，或在非零子类型上定义模型量；不能因为 Lean 名称叫 valuation 就抹掉这一约定。

固定源码 `NumberTheory/LocalField/Basic.lean` 定义 `IsNonarchimedeanLocalField K`，要求 `[Field K] [ValuativeRel K] [TopologicalSpace K]`，并继承估值拓扑、局部紧性及非平凡估值。它导出 DVR 整数环、有限剩余域、离散秩一等性质；在相容 uniform space 下导出完备性。这是实际局部域的通用框架，但不自动指定混合特征、`ℚ_p` 嵌入、ramification index 或 IUT log-shell。

本机 `NumberField.FinitePlace` 另有真实 adic completion 及整数环 DVR；不应因为有这些对象，就声称所有 normalized order、tensor packet 和 logarithm image 已连接。对本机 Padics 子目录的定向搜索没有找到满足 IUT 小分歧 log-image 结论的现成通用定理；这里只报告未找到，不宣称整个 Mathlib 不可能已有任何别处的相关结果。

## 5. `PreservesLayers` 与真实 shell 保持之间的义务

现有 `LocalNumerics.lean:19` 定义：

```lean
∀ (n : Int) (x : X), step * n < v (f x) ↔ step * n < v x
```

它直接要求所有整数阈值的**双向**保持。真实线性代数可以先做到“所有 `p^n L` 的保持”，但要把这转成当前有限整数 v 的严格阈值，还必须证明层集合的对应。现有模型没有隐藏这一对应为结论；它确实把层保持作为显式假设。因此不能把模型条件定理直接当作 shell 保持已足够的认证。

至少区分以下情况：

1. **只给 `f '' L ⊆ L`**：即使 f 是基域上的线性同构，这通常也只给缩放层的正向包含。候选回归测试是 `f(x)=p*x`、`L=ℤ_p⊆ℚ_p`；逆映射不能保持 L。该例仍须在独立 Lean 工程正式实现，不能借此宣布原 IUT 允许的 automorphism 真的只有单向包含。
2. **给 `f '' L = L`、且 f 与 p 的所有整数幂交换**：可用第 3 节接口推出所有 `p^n L` 的集合等式。这是纯线性代数层，不需要把最终估值上界作假设。
3. **L 是任意 `ℤ_p` 格**：得到的是该格的离散 gauge/过滤，不自动是场的 normalized order。只有在该格被证明等于适当 valuation ball/ideal 时，才可能匹配 `PreservesLayers`。
4. **L 等于整数环但有分歧**：`p^n O_K` 对应 `ord≥n`；`ord>n` 对应 `p^n 𝔪_K`。二者不能因“离散”而当成同一集合；分歧时 `𝔪_K` 通常不是 `pO_K`。如果实际 shell 是别的分式理想，必须按它自己的阈值计算。
5. **当前 X 包含 0、v 仍取 Int**：不能同时当作通常带 +∞ 的 valuation。需限制非零输入，证明 f 的像仍非零，再给整数清分母映射；或改用含零球的接口后单独取非零数值层。

与原稿数值相连的一条**候选**小分歧桥接为：p 为奇素数，`e≤p−2`，`ord(p)=1`，非零值群为 `(1/e)ℤ`，且已经独立证明

```text
log(O_K×) = {0} ∪ {x≠0 | ord(x)≥1/e}
I = (2p)^(-1) log(O_K×)
```

则预期 I 对应含零球 `{0} ∪ {ord>−1}`，而 `{0} ∪ {ord>n}=p^(n+1)I`。因此线性同构严格保持 I 时可把 p 幂缩放的集合等式迁移到整数严格层。这里的解析 log-image、离散值群、标量归一化、零点和清分母仍全是独立义务。**本报告没有证明该解析桥接，也没有核实原 IUT 所有允许作用均满足此处的线性/集合等式前提。**

该拆分有实际价值：不再把所有严格层保持整个塞进一个结构字段，而把可由线性代数推导的部分与尚待证明的分析识别分开。它也防止通过直接假设目标估值上界来制造形式化循环。

## 6. 公开 LANA 源码：实际读到的接口与版本冲突

[LANA-Project/iut4-sec1 README](https://raw.githubusercontent.com/LANA-Project/iut4-sec1/main/README.md) 明示只覆盖 IV §1 的部分独立数学，不验证 IUT；[toolchain](https://raw.githubusercontent.com/LANA-Project/iut4-sec1/main/lean-toolchain) 为 **4.32.0**。公开 [实施规范](https://github.com/lana-agents/iut/blob/main/Plans/Iut4Sec1Spec.md) 把 P10 的 log-lattice、P11 的体积列为后续门槛，并记录短 commit `c646cd5` 的 P6 构造工作。它提供值得跟踪的构造路线，不是本机已验收定理。

此次 GitHub API、固定短 SHA 页面及若干具体模块 raw 读取失败；本机直接 HTTPS 尝试被代理 socket 权限限制，web 工具对多个模块返回 cache miss。因此本轮**未取得这些具体模块的完整固定 SHA 源码**，不能报告其当前精确 lemma 名称或把 README 中的 planned 实现当成已读 proof term。

成功读到的 [lana-agents/iut 的 LocalTheory.lean raw](https://raw.githubusercontent.com/lana-agents/iut/main/Iut/Concrete/LocalTheory.lean) 是一个 **285 行缓存版本**，其内：

- `completionAt` 使用真实数域有限位完备化；这部分对象有具体来源。
- `LocalTensor.Tensor` 仍作为任意交换环/拓扑类型的字段给出，不凭字段注释就成为实际张量积。
- `LocalTheory` 仍把 `ordp_p`、`logShell_eq_integral`、`indAut_logShell`、`prop14_iii`、`prop14_iv` 等命题作为输入字段；`indAut_logShell` 只有像的单向包含。

与之相对，同路径 GitHub 搜索结果显示 **80 行较新版本**，README 也宣称已由 `LocalConstruct/*` 构造若干接口。新旧缓存明显不同，**不能把 285 行旧接口作为当前 main 的确切状态，也不能用新版 README 替旧接口补上证明**。必须取得某一完整 SHA，再逐 import 复核各字段的构造和 proof terms。

旧缓存的 `indAut` 甚至只是函数集合；其 `prop14_iv` 注释把“代数自同构保持整元素”用作解释，但实际类型没有使每个 φ 自动成为代数同构。这尤其不能作为普通 `ℚ_p` 线性 shell automorphism 保持整个 maximal order 的现成证明。后续应核对新版到底使用线性映射、代数映射还是独立 tensor factor 的格自同构。

任何依赖这些字段的后果只能登记为“给定该 `LocalTheory` 的条件式”。在构造并检验其真实实例之前，不能把所需局部估计作为已经补齐的数学事实。公开项目声称 `sorry`-free 并不消除这种前提审计。

## 7. 交付给后续实现的最小任务

1. 在匹配 rc2 的独立工程里实现 `LinearEquiv` + `Set.image_smul_comm` 的集合缩放恒等式；实例可直接取真正 `ℚ_[p]` 向量空间，避免完全无实例的 action 模型。
2. 定义真实 `Submodule ℤ_[p] M` 或实际整数理想；分别确认 `n:ℕ` 与 `n:ℤ` 两种缩放需要的标量结构。
3. 用 `PadicInt.norm_le_pow_iff_mem_span_pow` 建一个实际 p 进整数理想的 filtration 实例；同时记录它只涉及基域 `ℚ_p`，不冒充带指定分歧的 K。
4. 独立表达解析 bridge；在小分歧 log-image 尚未正式化时把它留为显式未证目标，并确保目标本身不是候选定理的假设字段。
5. 对当前四分量 `LocalNumerics`，给出非零值域、单位 `1/105` 和允许映射的真实精化；在这些精化完成以前，严格层模型仍只作条件机制模型。
6. 取得 LANA 固定 SHA/完整相关源文件后再决定复用；本轮网络/缓存限制记入此报告，未取得者不可准入。

本轮新增 fact-tree 节点数：**0**。未证明真实 shell 的分析识别，未解决 IUT 局部争点，未证明 abc。
