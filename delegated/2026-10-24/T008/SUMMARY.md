# T008 · SUMMARY

**状态：`RESEARCH_ONLY`**（报告类；PROTOCOL 规定来源类结论先按 RESEARCH_ONLY 返回）

## 目标

整理真实 `subtype`、`reduceMu`、`decompositionMap`、`muAction` 的类型及每条连续性输入；
交付可逐项对照、每条标注「已构造 / 仍为假设」的箭头表。

## 实际结果

- **箭头表 23 条**（`ARROW-TABLE.md` §3）：**已构造 18 条**（A01–A18），**仍为假设 5 条**（A19–A23）。
- 四个对象的**完整 Lean 类型**逐条给出（§1），来源行号可查；`probe/T008Probe.lean` 在
  `lake env lean -DwarningAsError=true` 下 **exit 0、零 error、零 warning、零 sorry**
  （`logs/probe.stdout.log`），11 条 `#print axioms` 全部只含
  `propext / Classical.choice / Quot.sound`。
- **连续性输入共 6 条**（§2，C1–C6）。其中 5 条是自由的（子群包含、离散拓扑、`continuous_id`、
  以及右腿 `hcomp` 由 `muAction` 的 `compHom` 定义直接 `rfl`）；
  **唯一的实质项是 C2：`Continuous decompositionMap`，且只被右腿需要**，额外前提 `[Algebra.IsIntegral F Ω]`。

## 准确前提

- A02/A07 需 `hk` **且** `[Algebra k (ResidueField A)]` **且** `hkres` 三者同时在场；缺 `hkres`
  则 `smul_algebraMap` 不成立、`decompositionMap` 根本构造不出来。
- A12（左腿）**不需要** `[Algebra.IsIntegral F Ω]`；A13（右腿）需要。两条腿强度不同，不可合并陈述。
- A14（方块交换）另需 `[Algebra.IsIntegral k κ]`、两侧 `[HasKummerRoots n _ _]`。
- A16（`decompositionMap` 满射）需 `[IsGalois F Ω]`、**`[IsAlgClosed Ω]`**、`[Algebra.IsIntegral k κ]`
  与 `hres`（`A ∩ F` 的残值落在 `k` 内 = 该位是 `k`-有理点）。**不是无条件满射**。
- `muAction` 必须经 `letI` 消费；忘记 `letI` 会静默落到 `Mu n κ` 上 `Gal(κ/k)` 的**另一个**作用实例。

## 是否推进首个缺箭头

**否。** 本任务是类型台账，不构造新映射。它把一个此前易混的边界钉死：
**反射不走 `reduceMu` 的逆，而走右腿 `decompositionMap` 的单射（A18）**；
而 A18 的强度完全由 A16 的强前提封顶。所以方块交换在被证明的同时，
**其可用性仍被 `[IsAlgClosed Ω]` + `k`-有理点限制**，这一点在台账里不可省略。

## 未解决内容

1. **A19**：`reduceMu` 的单/满/等价在工作区**无任何声明**。设计上不需要；但若下游要断言可逆，须另证。
2. **A20**：`decompositionMap` 满射在**非代数闭 `Ω` / 非有理点**情形无已构造结果；
   因此「右腿 = inflation」在一般情形**未证**（还需先做 `D_A/ker ≅ G_κ` 的商识别并核商作用）。
3. **A21**：`Boundary/DecompositionBridge.lean` 在 `baseline.json` 中，但**无 `.olean`**，
   本工作区无法 elaborator-核验其 `reducedClass` / `residue_kummer_eq_of_reduced_restrictions_eq`。
   按「代理自报 ≠ 已验证」记为假设而非已构造。
4. **A22**：原始 tempered `Π^tp_Ÿ` 与 `Δ_Θ` 明确 out of scope（`Iut/EtaleTheta/README.md` S2 决策、
   `KummerClass.lean:19-22`），本方块与原始 Θ-link 之间**无已构造箭头**。
5. **A23**：Wall `(9-1)` 在 `Iut/Wall/EtaAlg.lean` 中是**结构字段 + `Prop` 假设**，从不被证明。
   本方块不提供通往该链的接口。

**不宣称**：IUT 核心争议、Corollary 3.12、abc 的任何部分被解决；不宣称任何 fact-tree 准入。
