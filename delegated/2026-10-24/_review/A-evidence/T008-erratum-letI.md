# 勘误 2：T008 关于 `letI` 的论述方向错误（主线独立复现）

日期：2026-10-24。来源：独立审查官 B（`_review/B-semantics/T008.md`）。
主线**另起一次运行独立复现**，未采信转述。

## 1. 交付方的原话

`delegated/2026-10-24/T008/SUMMARY.md` 与 `ARROW-TABLE.md` §1.3 写：

> `muAction` 必须经 `letI` 消费；忘记 `letI` 会**静默落到** `Mu n κ` 上 `Gal(κ/k)` 的**另一个作用实例**。

## 2. 实测：不是"静默落到另一个实例"，而是**硬错误**

审查官 B 写了三组对照探针（`BLetIProbe.lean`）：

- P2：在**没有** `letI` 的作用域里 `#synth MulDistribMulAction ↥(decompositionSubgroup) (Mu n κ)`
- P1：把 `reduceMu_smul` 的**命题**写在无 `letI` 的作用域里
- P3：对照组，命题前加 `letI := muAction F A hk hkres n`

主线在 `candidates/core-kummer` 内独立复跑同一文件：

```text
argv:  lake env lean .wt/leti-check/BLetIProbe.lean
exit:  1
elapsed: 50.3 s
stdout: BLetIProbe.lean:31:0: error: failed to synthesize
          MulDistribMulAction (↥(ValuationSubring.decompositionSubgroup F A)) (Mu n (ResidueField ↥A))
        BLetIProbe.lean:35:66: error(lean.synthInstanceFailed): failed to synthesize instance of type class
          HSMul (↥(ValuationSubring.decompositionSubgroup F A)) (Mu n (ResidueField ↥A)) ?m.66
```

P3（带 `letI`）不报错，证明错误**只**来自缺 `letI` 这一处。

## 3. 为什么"静默换实例"不可能发生

审查官 B 全扫 `Iut/` 后指出：工程里根本没有可被"误落"的第二个目标实例。

| 位置 | 内容 | 是否可被误落 |
|---|---|---|
| `ContinuousKummerTheory/Kummer/Basic.lean:86` | 作用群是 `Gal(Ω/K)`，**不是** `Gal(κ/k)` | 否，群不同 |
| `ContinuousKummerTheory/Kummer/Decomposition.lean:140` | `muAction` 是 `def` + `@[implicit_reducible]`，**不入实例搜索** | 否，不是 `instance` |

所以 Elaborator 找不到任何实例可消解 → 直接失败。**"两个作用在数值上恰好一致"这个说法
（审查官 A 上一轮已指出措辞偏重）实际上连"落到另一个实例"这一步都不会发生。**

## 4. 正确表述

应写为：

> `muAction` 是 `def` 而非 `instance`，所以消费它的命题**必须**用 `letI := muAction …` 把实例引入作用域；
> 缺这一步是**编译期硬错误**（`failed to synthesize MulDistribMulAction …`），不是静默换实例。

## 5. 这条错误的性质

- 这**不影响** T008 的箭头计数、A16 前提、A12/A13 两腿强度、C2 唯一实质、A21 等其余自述；
  审查官 B 复核后确认"其余 4/5 自述正确，23 条无错标"。
- 它属于**机制解释错误**，不是事实伪造：交付方观察到"必须写 `letI`"这个现象是对的，
  只是把"不写会怎样"说反了。真正后果比它说的**更轻**（直接编译失败，不会悄悄用错实例）。
- T008 仍维持 `RESEARCH_ONLY`；仍不授予任何准入。

## 6. 与勘误 1 的关系

勘误 1（`T008-erratum.md`）处理的是**计数口径**（18 → 约 16）与 A14/A15 的引理委托披露。
本条处理的是**机制表述**。两条都来自独立审查，都不改交付方原件。
