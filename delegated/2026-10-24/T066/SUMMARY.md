# T066 · `MonoThetaKummer` 与 `cyclotomicRigidity` 来源审计

状态 **`RESEARCH_ONLY`**。静态来源审计，未编译、未运行 Lean、未进编辑器、未进 fact-tree。
只读 `delegated/2026-10-24/T066/`；未改主线源码、Boundary、中央 fact-tree。

## 目标与结果

按卡片要求，逐一标定两组对象用到的**已给环境**、**已给同构**、以及**尚未构造**的输入，并给出准确类型、源码 SHA 与构造路径。

**核心结论（一句话）：两个模块都没有构造自己的输入。** `cyclotomicRigidity` 的环境 `E` 与同构 `f : E ≅ model` 是假设；`MonoThetaKummer` 的四个字段 `envF / envD / kum / perm` **全部**是字段即假设。全仓库里 `MonoThetaKummer D` 只有一个居民 `const`，它把所有环境取成同一个 `E`、所有同构取成恒等——类型的可居性是有了，但关于 `n,mHT` 什么都没见证。

## 计数

| 类别 | 数量 | 说明 |
|---|---|---|
| 已给（PARAMETER） | **12** | `MonoThetaKummer` 4/4 字段；`BiCoricKummer` 4/4 字段；`cyclotomicRigidity` 的 `{E}` 与 `f`；`RigidDGalStrip.kappa`；`StripKummer` 参数块 |
| 尚未构造（NOT_CONSTRUCTED） | **6** | 见下「关键缺口」 |
| 已构造（CONSTRUCTED） | **9** | `Env.mu/taut/L/thetaSplit/IsCyc`、`MonoThetaKummer.const`、`horizMap/vertMap`、`envIsoRefl` |

12 / 6 / 9 是**导航用计数**，不是不变量；承重的是 `source-audit.json` 里逐字段的 tier 标注。

## 准确的「已给」清单（`MonoThetaKummer`，`Thm311Rest.lean:270`）

```
envF : (ℤ×ℤ) → ∀ w : FinitePlace D.Fmod, w ∈ D.VBad → Env.{0}
envD : ℤ      → ∀ w : FinitePlace D.Fmod, w ∈ D.VBad → Env.{0}
kum  : ∀ (n m : ℤ) (w) (hw : w ∈ D.VBad), Env.Iso (envF (n,m) w hw) (envD n w hw)
perm : ∀ (n : ℤ)   (w) (hw : w ∈ D.VBad), Env.Iso (envD n w hw) (envD (n+1) w hw)
```

`kum`、`perm` 都是 `Env.Iso` 值，由调用方提供。**它们是假设，不是构造**——这正是卡片禁止的「把已有同构参数当作已构造的来源」。源码文档字符串亦自陈（`:92`）：这些环境是 `BiCoricKummer` / `MonoThetaKummer` 的 **data**，不是从 `D^⊢`-prime-strip 或 theater 的 tempered Frobenioid 构造的。

## 准确的「已给」清单（`cyclotomicRigidity`，`CyclotomicRigidity.lean:364`）

```
theorem cyclotomicRigidity (hμ : AddMonoid.IsTorsion μ) {E : Env.{u}}
    (f : Env.Iso E (model M l μ red ρ)) : … 
```

`f` 是**前提**。该定理只断言算法是**自然的**（给定与模型的同构，算法输出被搬过去），不断言环境可被重构。

一处必须点明的形式落差：`Env.IsCyc`（`:112`）是**关系** `t ∈ taut ∧ m ∈ mu ∧ t+m ∈ thetaSplit`，不是映射。全仓库没有任何 `(l·Δ_Θ)⊗ℤ/N ≃ μ_N` 的 `≃+`。引用时应说「该同构的图，以关系形式形式化」，不能说「该同构」。

## 关键缺口（`GAP-T066-1`）

**从未从初始 Θ-数据构造 `envF`/`envD`/`kum`/`perm`。**

```
MISSING:  buildMonoThetaKummer : (D : InitialThetaData.{0}) → (L : LogThetaLattice D) → MonoThetaKummer D
          使 envF 与 n,mHT 的 tempered Frobenioid 给出的 mono-theta 环境投射系统一致
          （[IUTchII] Prop. 3.3 / 3.4），kum/perm 为 [IUTchIII] Prop. 2.1(iii) 的同构。
```

六项未构造输入：

1. **N1** 由曲线/ tempered 群构造的 `Env` —— `Iut/` 内不存在任何由数据产出的 `Env` 项。
2. **N2** `Env.Iso E model` —— 只以参数出现。
3. **N3** 作为映射的 cyclotome 同构 —— 只有关系 `IsCyc`。
4. **N4** 非交换 `Π^tp_Y[μ_N]` 的 cyclotomic rigidity —— README 列为 research-level。
5. **N5** 真正的 étale theta 类 `η^Θ ∈ H¹(Π^tp_Ỹ, Δ_Θ)` —— README S2'。
6. **N6** 由 tempered Frobenioid 到 `envF`/`envD` 的来源，以及由 étale-picture 置换对称性到 `kum`/`perm` 的来源。

补齐它需要：S2'（无限 tempered 覆盖上没有结构层，`Θ̈` 不在任何有限层上）、S3（`Env` 与 `Π^tp_Y[μ_N]` 的认同，即 Cor. 2.18(i) 的 tempered 远阿贝尔重构）、实际环境的投射系统与离散刚性（现只有模型塔）、以及 S5（tempered Frobenioid 幺半群与真实 theta 除子的一致性）。

## 不构成缺口的（防误读）

`Env.mu / taut / L / thetaSplit / IsCyc`、`horizMap / vertMap`、`gal`、`liftIso`、`factorGal` **都是构造出来的**；`map_mu / map_taut / map_L / map_thetaSplit / isCyc_iff / isCyc_horizMap / isCyc_horizMap_aut / isCyc_vertMap / isCyc_of_rigid` **都证明了**。本审计只否定「它们提供自己的输入」，不否定这些结论。

## 基线核查（卡片的硬要求）

`baseline.json` 有 100 条文件记录，但**没有钉住定义 `MonoThetaKummer` 的那个文件**。被钉住的只有 `CyclotomicRigidity.lean`（`69205310…`）与 `StripKummer.lean`（`a7b091c5…`）。`Thm311Rest.lean`、`MonoTheta.lean` 均不在其中。故本审计的 file identity 另立：文件 SHA256 逐项实测，并以 `git rev-parse HEAD:<path>` 的 blob id 对钉住的提交 `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb` 复核（worktree clean）。

卡片原文已预警此事（`文件名相同不算版本相同`、`前序的实际源码与收据SHA必须另行取得`）。下游引用请用 `source-audit.json` 的 `sources[].sha256`，不要引 baseline——那里没有这一条。

另：`reviews/core-round/external/lana-agents--iut/` 下有**字节相同**的副本（同一 SHA256）；`Takkun-kohinata--IUT_LEAN/IutLean/Anabelian/CyclotomicRigidity.lean` 是**另一个** 5320 字节文件（`2a7f29de…`），不可混同。

## 与前序审计的关系

`native-source-square.md`（`StripKummer` 五字段皆输入，`trivial` 不能代替原始箭头）与 `GAP-shared-anchor-source.md`（`已有 MonoThetaKummer 等结构的字段是输入，不能当作第1–2项的来源构造`）与本审计一致；本审计把同一判定推进到 `MonoThetaKummer` 与 `cyclotomicRigidity` 本身，并补上逐字段 tier、逐文件 SHA、以及 `const` 的退化性说明。

本卡**不**关闭该缺口，**不**改变 Step (xi)、Corollary 3.12 或 abc 的 OPEN 状态。

## 交付

- `SUMMARY.md`（本文件）
- `source-audit.json` —— 30 条来源、逐字段 tier、6 项未构造输入的完整类型、8 项交叉核查
- `delivery.json` —— 任务卡/baseline/file SHA、实际命令 argv/cwd、退出码、耗时、完整 stdout/stderr
- `replay.ps1` —— 只读重放：32 个 pin 的 SHA256+字节、上游 HEAD 与 worktree 清洁度、9 个声明的行位
- `logs/replay.stdout.log`、`logs/replay.stderr.log` —— 实际运行日志

`replay.ps1` 实测：`RESULT: ALL_PINS_OK`，exit 0。

## 范围声明

静态源码阅读。是否在 `f7ed1cc` 真能编译未在此重新建立——钉住的 checkout 清洁是必要条件，不是充分条件。本任务不产出 Lean 文件，故不附公理日志；`declarations` 中的 `type` 字符串是**源码的类型**，不是本任务的断言。无编辑器准入，无 fact-tree 准入。
