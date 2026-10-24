# T008 · 实际分解群方块：类型台账

**状态：`RESEARCH_ONLY`。** 本文件只整理类型与箭头，不证明新数学，不关闭任何核心 gap，不授予 fact-tree 准入。

所有类型均取自**实际源码**，并由 `probe/T008Probe.lean` 的 23 条 `#check` + 11 条 `#print axioms` 在
`-DwarningAsError=true` 下打印（`logs/probe.stdout.log`，exit 0，零 error，零 warning，零 sorry）。
凡未跑过 elaborator 的条目，本文明确标注其证据层级（例如 §3.1 的上游读数）。

---

## 0. 记号

| 记号 | 真实 Lean 项 |
|---|---|
| `Ω, F, k` | 三个 `Field`，带 `[Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]` |
| `A` | `A : ValuationSubring Ω`，附 `hk : ∀ c : k, algebraMap k Ω c ∈ A` |
| `κ` | `ResidueField A`（即 `IsLocalRing.ResidueField ↥A`） |
| `residue` | `IsLocalRing.residue A : A →+* κ` |
| `D_A` | `↥(ValuationSubring.decompositionSubgroup F A) = ↥(MulAction.stabilizer (Ω ≃ₐ[F] Ω) A)` |
| `G` | `Gal(Ω/F) = Ω ≃ₐ[F] Ω` |
| `G_κ` | `Gal(ResidueField A/k)` |
| `M_Ω`, `M_κ` | `Mu n Ω`, `Mu n (ResidueField A)`（皆 `⊥` 拓扑 + `DiscreteTopology`） |

两处「自由前提」在本文件中指：不需要数学输入，只由类型类/定义给出。

---

## 1. 四个对象的真实类型（elaborator 输出）

### 1.1 `subtype`

```
@Subgroup.subtype : {G : Type u_4} → [inst : Group G] → (H : Subgroup G) → ↥H →* G
```

`D_A` 是 `Gal(Ω/F)` 的**子群**（`Mathlib/RingTheory/Valuation/RamificationGroup.lean:30-31`，`MulAction.stabilizer`），
所以 `(A.decompositionSubgroup F).subtype : D_A →* Gal(Ω/F)` 是**包含**，不是商映射。
这一点在台账里必须钉死：`ContH1.map` 的群变量方向是 `H →* G`（协变收缩），
右腿因此是「沿 `decompositionMap` 的 pullback」，把它叫 inflation 需要先做商识别（见 §3 的 A16/A20）。

### 1.2 `decompositionMap`

```
@decompositionMap : {k} → (F : Type u_5) → {Ω} →
  [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω] →
  (A : ValuationSubring Ω) → (hk : ∀ c : k, (algebraMap k Ω) c ∈ A) →
  [inst_7 : Algebra k (ResidueField ↥A)] →
  (∀ (c : k), (residue ↥A) ⟨(algebraMap k Ω) c, ⋯⟩ = (algebraMap k (ResidueField ↥A)) c) →
  ↥(ValuationSubring.decompositionSubgroup F A) →* Gal(ResidueField ↥A/k)
```

**每条输入**：

| 输入 | 作用 | 能否省 |
|---|---|---|
| `F : Type*`（显式） | 决定 `Gal(Ω/F)`，进而决定 `D_A` | 不能，显式参数 |
| `hk : ∀ c : k, algebraMap k Ω c ∈ A` | 让 `algebraMap k Ω` 落到 `A` 里，从而可复合 `residue` | 不能 |
| `[Algebra k (ResidueField A)]`（实例参数） | `Gal(κ/k)` 需要 `κ` 是 `k`-代数 | 不能；**注意它是 `instance` 参数，可被本地 `letI` 换掉** |
| `hkres` | 保证该代数结构与 `residue ∘ algebraMap` 一致；`smul_algebraMap` 靠它证明 `D_A` 在 `k` 上作用平凡 | 不能，否则 `decompositionMap` 不是 `AlgEquiv` |

**关键实现事实**（`Decomposition.lean:78-83`）：
`toFun σ := AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ (ResidueField A) σ) (smul_algebraMap … σ)`。
即 `decompositionMap` 的底层就是 `σ` 在 `κ` 上的 `MulSemiringAction`，`map_one'`/`map_mul'` 由 `one_smul`/`mul_smul` 给出。
由此 `decompositionMap_apply : decompositionMap σ x = σ • x` 是 **`rfl`**，不是定理。

**陷阱**：`hkres` 以「匿名实例」形式出现（无名字的 `( … )` 参数），
而 `[Algebra k (ResidueField A)]` 是实例参数。若下游另给一个 `k`-代数结构而不补匹配的 `hkres`，
`smul_algebraMap` 不成立，`decompositionMap` **构造不出来**（不是构造出来但性质变弱）。

### 1.3 `muAction`

```
@muAction : {k} → (F : Type u_5) → {Ω} → … (A) (hk) → [Algebra k (ResidueField ↥A)] → (hkres) →
  (n : ℕ) → MulDistribMulAction (↥(ValuationSubring.decompositionSubgroup F A)) (Mu n (ResidueField ↥A))
```

**它是 `def`，不是 `instance`**（`@[implicit_reducible] noncomputable def`），生产代码一律
`letI := muAction F A hk hkres n` 取用（`Decomposition.lean:165,183,188,202,208`；`KummerClass.lean:174`）。

**类型层面它不携带任何超出 `decompositionMap` 的数据**：
```lean
MulDistribMulAction.compHom _ (decompositionMap F A hk hkres)
```
所以 `d • ζ`（在 `muAction` 下）**按定义**等于 `(decompositionMap d) • ζ`（在 `Gal(κ/k)` 作用下）。
这正是右腿 `hcomp` 能用 `fun _ _ => rfl` 关掉的原因（见 §2 的 C6）。

**陷阱（必须在台账里写明）**：`Mu n κ` 本身已由 `Basic.lean:86-91` 对 `Gal(κ/k)` 给出一个
`MulDistribMulAction` 实例。若忘记 `letI := muAction …`，`ContH1.map` 的 `hcomp` 与
`reduceMu_smul` 里的右侧 `σ •` 会落到**另一个**作用上，语句变成不同命题（通常无法关闭，偶有歧义实例时更危险）。
`reduceMu_smul` 的陈述内部先 `letI := muAction F A hk hkres n`（`:165`），消费方必须复现同一 `letI`。

### 1.4 `reduceMu`

```
@reduceMu : {Ω : Type u_4} → [inst : Field Ω] → (A : ValuationSubring Ω) → (n : ℕ) → n ≠ 0 →
  Mu n Ω →* Mu n (ResidueField ↥A)
```

**每条输入**：

| 输入 | 作用 | 能否省 |
|---|---|---|
| `A : ValuationSubring Ω` | 提供 `A.toSubring`、`residue A` | 不能 |
| `n : ℕ`, `hn : n ≠ 0` | 唯一数学输入：`A` 对 `n` 次根封闭 | 不能；`hn` 经 `mem_of_pow_mem_toSubring` → `ValuationSubring.mem_of_pow_mem` |
| `[Field Ω]` | 唯一类型类 | 由上下文给出 |

**与 `k`、`F`、`Gal` 全无关**：`reduceMu` 不出现 `k`、`F`，也不需要分解群。
它是 `specMu` 的一个实例：
```
@specMu : (n : ℕ) → {Ω} → {Ω'} → [Field Ω] → [Field Ω'] → (B : Subring Ω) →
  (∀ β : Ω, β ^ n ∈ B → β ∈ B) → (B →+* Ω') → Mu n Ω →* Mu n Ω'
```
取 `B := A.toSubring`、`hB := mem_of_pow_mem_toSubring A n hn`、`ψ := residue A`。

**`reduceMu` 的连续性输入是空的**：`Mu` 两侧拓扑都是 `⊥`（`Basic.lean:55`）且 `DiscreteTopology`（`:57`），
故 `Continuous (reduceMu A n hn)` 由 `continuous_of_discreteTopology` 关闭，**不含任何数学**。

---

## 2. 每条连续性输入

`ContH1.map` 的签名（`ContH1/Basic.lean:188-189`）要求三件事：`hφ : Continuous φ`、`hf : Continuous f`、
`hcomp : ∀ h m, f (φ h • m) = h • f m`。下面逐条列出本方块实际付了什么。

| 编号 | 连续性/相容性输入 | 具体给法 | 是否实质 |
|---|---|---|---|
| **C1** | `Continuous (A.decompositionSubgroup F).subtype` | `continuous_subtype_val`（子空间拓扑） | **自由** |
| **C2** | `Continuous (decompositionMap F A hk hkres)` | `continuous_decompositionMap`，**额外需要 `[Algebra.IsIntegral F Ω]`** | **实质** |
| **C3** | `Continuous (reduceMu A n hn)` | `continuous_of_discreteTopology`（`Mu` 两侧皆 `⊥`） | **自由** |
| **C4** | `Continuous (MonoidHom.id (Mu n (ResidueField A)))` | `continuous_id` | **自由** |
| **C5** | 左腿作用相容 `hcomp` | `reduceMu_smul F A hk hkres n hn` | 准自由（定义级，但需 `letI := muAction`） |
| **C6** | 右腿作用相容 `hcomp` | `fun _ _ => rfl` | **自由**（`muAction` 由 `decompositionMap` 经 `compHom` 定义） |

### 这张表的主要结论

**整个方块里唯一实质的连续性是 C2。** 而且 C2 只被**右腿**需要：
左腿的群映射是子群包含（C1 自由），系数映射是 `reduceMu`（C3 自由）；
右腿的群映射是 `decompositionMap`，其 Krull 拓扑连续性才是真内容，
证明见 `Decomposition.lean:107-131`：用 `krullTopology_mem_nhds_one_iff` 把单位邻域降到有限 Galois 中间域，
再用 `stabilizer_isOpen_of_isIntegral` 取 `κ` 的有限生成元素提升的稳定化子。

**推论（供后续任务用，本身不构成新定理）**：
若某条路线只需要左腿，则它**不需要** `[Algebra.IsIntegral F Ω]`；
一旦要右腿或要「沿 `decompositionMap` 的 pullback 是单射」（A18），`[Algebra.IsIntegral F Ω]` 就回到前提里。
台账若把两条腿的前提混写，会把左腿的强度虚报成右腿的强度。

---

## 3. 箭头表

状态只有两档：**已构造** / **仍为假设**。带更强前提的「已构造」在备注里逐项列出——
按 PROTOCOL，这不等于该结论在其强形式下成立。

| # | 箭头 | 真实签名 / 出处 | 状态 | 备注（前提、方向、陷阱） |
|---|---|---|---|---|
| A01 | `D_A ↪ G` | `(A.decompositionSubgroup F).subtype : D_A →* Gal(Ω/F)` | **已构造** | Mathlib `Subgroup.subtype`；包含非商映射 |
| A02 | `G ⟶ G_κ`（分解映射） | `decompositionMap : D_A →* Gal(ResidueField A/k)` | **已构造** | 需 `hk`、`[Algebra k κ]`、`hkres`；`Decomposition.lean:78` |
| A03 | A02 的逐点描述 | `decompositionMap_apply : decompositionMap σ x = σ • x` | **已构造** | `rfl` |
| A04 | A02 与 `residue` 自然 | `decompositionMap_residue : decompositionMap σ (residue b) = residue (σ • b)` | **已构造** | 由 `ResidueField.residue_smul` |
| A05 | A02 的核 | `ker_decompositionMap : (decompositionMap).ker = A.inertiaSubgroup F` | **已构造** | `Decomposition.lean:93`；与 Mathlib `inertiaSubgroup` 对齐 |
| A06 | A02 的连续性 | `continuous_decompositionMap [Algebra.IsIntegral F Ω] : Continuous ⇑decompositionMap` | **已构造（带前提）** | 前提 `[Algebra.IsIntegral F Ω]`；见 C2 |
| A07 | `D_A` 作用到 `M_κ` | `muAction : MulDistribMulAction D_A (Mu n (ResidueField A))` | **已构造** | `= compHom _ decompositionMap`；必须 `letI` |
| A08 | `M_Ω ⟶ M_κ`（系数约化） | `reduceMu A n hn : Mu n Ω →* Mu n (ResidueField A)` | **已构造** | 仅需 `hn : n ≠ 0`；不涉及 `k,F,Gal` |
| A09 | A08 的一般引擎 | `specMu n A.toSubring hB (residue A)` | **已构造** | `specMu` 需 `hB : ∀ β, β^n ∈ B → β ∈ B` |
| A10 | A08 的 `D_A`-等变 | `reduceMu_smul : reduceMu (subtype σ • ζ) = σ • reduceMu ζ` | **已构造** | 需 `letI := muAction`；经 `specMu_smul` + `residue_smul_eq` |
| A11 | A09 的一般等变 | `specMu_smul : specMu (ι d • ζ) = d • specMu ζ` | **已构造** | 需 `hDact : d • ζ = π d • ζ` 与 `hψ` |
| A12 | **左腿** `H¹(G,M_Ω) → H¹(D_A,M_κ)` | `ContH1.map (subtype) C1 (reduceMu) C3 C5` | **已构造** | 前提：C1（自由）、C3（自由）、C5；**不需要 C2** |
| A13 | **右腿** `H¹(G_κ,M_κ) → H¹(D_A,M_κ)` | `ContH1.map decompositionMap C2 (MonoidHom.id) C4 (fun _ _ => rfl)` | **已构造（带前提）** | 前提：C2 → 需 `[Algebra.IsIntegral F Ω]` |
| A14 | **方块交换** | `decomposition_kummer`：`A12 (κ_F f) = A13 (κ_k a)` | **已构造（带前提）** | 前提：`f : Fˣ` 在 `A` 内可逆、`residue f = algebraMap a`；`[Algebra.IsIntegral F Ω]`、`[Algebra.IsIntegral k κ]`、`[HasKummerRoots n F Ω]`、`[HasKummerRoots n k κ]`；`Decomposition.lean:180` |
| A15 | 值版本 | `decomposition_kummerValue`（`R →ₐ[k] k` 点 + `hRA` + `hRx`） | **已构造（带前提）** | 同 A14，另需 `x : R →ₐ[k] k` 与 residue 相容 |
| A16 | `D_A ↠ G_κ` | `decompositionMap_surjective` | **已构造（强前提）** | 前提：`[IsGalois F Ω]`、**`[IsAlgClosed Ω]`**、`[Algebra.IsIntegral k κ]`，及 `hres : ∀ a : F, algebraMap F Ω a ∈ A → ∃ c : k, residue a = algebraMap c`（该位是 `k`-有理点）。`DecompositionSurjective.lean:506`。**不是无条件满射** |
| A17 | A16 的中间引理 | `exists_decompositionMap_eq_of_fixes`（固定 `A ∩ F` 的残值者皆在像中） | **已构造（强前提）** | 同 A16 除 `hres`；`DecompositionSurjective.lean:439` |
| A18 | **右腿单射**（反射判据） | `CoreReducedComparison.pullback_injective φ hφ hsurj hcomp : Injective (ContH1.map φ hφ id continuous_id hcomp)` | **已构造** | 需 A16 供 `hsurj`；系数取 `MulEquiv.refl`；`Boundary/ReducedComparison.lean:16` |
| A19 | `reduceMu` 的单/满/等价 | —（工作区**无此声明**） | **仍为假设** | 工作区不存在 `Injective/Surjective/≃*` 形式的 `reduceMu`。设计上**不需要**它：`ReducedComparison.lean:4-5,22-23` 明确「反射走右腿单射，不经 `reduceMu` 的逆」。若后续任务要断言它可逆，必须另行证明，不能从 A08/A10 推出 |
| A20 | A16 在**非代数闭 `Ω` / 非有理点**的满射 | —（工作区**无此声明**） | **仍为假设** | A16 的 `[IsAlgClosed Ω]` 与 `hres` 是实质限制。在一般 Galois 闭包 + 非 `k`-有理位上没有任何已构造的满射/商识别，故「右腿 = inflation」在一般情形未证 |
| A21 | 残值侧恢复（消费者） | `CoreDecompositionBridge.residue_kummer_eq_of_reduced_restrictions_eq` | **仍为假设（未核）** | 文件 `Boundary/DecompositionBridge.lean` 在 `baseline.json` 中，但 `candidates/core-kummer/.lake/build/lib/lean/Boundary/DecompositionBridge.olean` **不存在**，本任务无法从该工作区 elaborator-核验。按「代理自报 ≠ 已验证」，这里不记已构造。见 `GAP.md` |
| A22 | 原始 tempered `Π` → 本方块 | —（明示 out of scope） | **仍为假设** | `reviews/core-round/external/iut/Iut/EtaleTheta/README.md:294-296`（S2 决策）与 `KummerClass.lean:19-22` 均明言 `Π^tp_Ÿ` 与 `Δ_Θ` 不在形式化范围内，该类只经「点与 germ 的限制」记录。故 A14 与原始 Θ-link 之间无已构造箭头 |
| A23 | Wall `(9-1)` | `Iut.Wall.EtaAlg.Wall` 是 `structure EtaAlg` 上的 `Prop`，`out`/`realisation` 为**字段** | **仍为假设** | `Iut/Wall/EtaAlg.lean:96-126,169-177`。`Wall` 从不被 `EtaAlg` 证明，只作假设被消费；`research/core-projective-2026-10-24/backward-delivery-review.md:24` 已独立指出。本方块（A01–A18）与该链**没有**已构造接口 |

**计数：23 条箭头 —— 已构造 18 条（A01–A18），仍为假设 5 条（A19–A23）。**

其中「已构造」里带额外前提、不可按强形式引用的是：A06、A13、A14、A15、A16、A17（6 条）。
A01–A05、A07–A12 无额外数学前提；A18 的强度上限 = A16（其 `hsurj` 由 A16 供给）。

### 3.1 不计入上表的上游读数（未核，仅备查）

`TateCurvesTheta.TateParameter.decomposition_kummer_thetaGerm`
（`reviews/core-round/external/tate-curves-theta/TateCurvesTheta/Kummer/ThetaGerm.lean:342`，
下游消费点 `reviews/core-round/external/iut/Iut/EtaleTheta/KummerClass.lean:173-184`）
形状与 A14 一致（取 `F ⊇ K⟦X⟧`、`ψ = residue A`、`hRx` 由 `residue_eq_pointEval` 供给）。

**它不进入箭头表**：该文件不在 `baseline.json` 的文件清单内，本任务也**没有构建** `tate-curves-theta` 工程，
因此既无 SHA 绑定、也无本任务自有编译证据。按 PROTOCOL「代理自报、材料预检、命令行通过与父线程实际编辑器准入是不同状态」，
这条只能作为源码读数备查，不得引用为「已构造」。

---

## 4. 与任务卡的对照

| 卡上要求 | 落实情况 |
|---|---|
| 真实 `subtype` 类型 | §1.1 + A01 |
| 真实 `reduceMu` 类型 | §1.4 + A08/A09 |
| 真实 `decompositionMap` 类型 | §1.2 + A02 |
| 真实 `muAction` 类型 | §1.3 + A07 |
| 每条连续性输入 | §2 全表（C1–C6） |
| 箭头表、逐项标已构造/假设 | §3（23 条） |

**未做**（见 `GAP.md`）：`Boundary/DecompositionBridge.lean` 的 elaborator 核验；`tate-curves-theta` 工程构建；
任何对 `reduceMu` 可逆性的判定；任何把 A22/A23 补成已构造的尝试。
