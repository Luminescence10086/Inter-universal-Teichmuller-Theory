# N03 — 核心目标的量词、类型与依赖清单

**这一页只说"要证什么"，不说"怎么证"，也不说它已被证明。** 目标本身出自报告原文（直引见下），
Lean 侧的对应接口只作为"已形式化的形状"，不作为内容上的证明。

## 1. 原文目标（逐字）

`research/round2-source-cache/LANA-interim-report-2026-07.txt`，§9.2，第 45–46 页，行 2138–2141：

> The main goal now is to relate these two kinds of isomorphisms: the one arising from `q` and the one
> arising from anabelian methods. Concretely, we wish to show that **there exists some suitable `S`** such that
> `η_q = η^anab_S`. (9-1)

同段（行 2123–2137）给出两块类型：

- `η^anab_S : R^val ∼→ R^ss`，依赖 `S ⊂ V^C(I_v)`，由 anabelian 方法构造；
- `R^ss = {T ⊂ V^C(I_v) | adelic and measurable}/∼`，`T ∼ T'` 当且仅当二者体积相同；`M = 1·S`（`1 ∈ N` 的作用），
  `R^ss` 中的**pilot** 取为 `M` 所在的类；
- `η_q : R^val ∼→ R^ss`，其目标侧 pilot 是 `{q_v O_v}` 沿对角线嵌入 `V^C(I_v)` 所得的类。

## 2. 目标的形式化形状（量词与类型）

设 `D` 为 BPS（`q`-BPS 与 `Θ`-BPS 在此只作为 `D` 的参数），`ι : A.Choice (A.qBPS h₂) h₁` 为选择，
`S : Ind3 D`。则目标陈述为

```
∃ S : Ind3 D,  A.etaAnab ι S = etaQ D
```

- **定义域/陪域**：两边都是 `R^val →ₗ[ℝ] R^ss`（点线之间的线性同构）；`etaAnab ι S` 与 `etaQ D` 是同类型的两张映射。
- **相等的含义**：作为**带 pilot 的实线之间的线性映射**相等；由 `ValBPS.eta_eq_eta_iff`，这等价于在 pilot 一点上相等。
- **量词次序**：`ι` 先被固定（`S` 的选择在给定 `ι` 之后），然后 `∃ S`。**不是** `∀ S`，**不是**「整个 `S` 族上读数不变」。
- 量词这一点是本任务最重要的产出：工程里此前把「沿轨道不变 ⇒ 下降到商」（W5/W7）当成 (9-1) 的**必要条件**，已被反例推翻
  （`research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean` 的 `existence_does_not_force_invariance`）。

## 3. Lean 侧已存在的对应（形状一致，内容不是）

`reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean:151`：

```
theorem etaAnab_eq_etaQ_iff {h₁ h₂ : A.Side} (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D) :
    A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs
```

即：**在 Lean 侧，(9-1) 被化归为一个实数等式**：`logVol(out ι S)` 是否等于 q-pilot 的左端。
这条定理把 ∃ 型目标变成 ∃-标量方程，但它**没有**给出该方程有解——这正是核心缺口。

## 4. 三类条件必须分开写

1. **充分条件**（能构造 `S` 就够）：存在 `S` 使 `logVol(out ι S) = qPilot.lhs`。
2. **必要条件**（原文确有来源支持的）：两图相等 ⟺ 在 pilot 处相等（`eta_eq_eta_iff`）；
   以及 `logVol` 与 `etaAnab` 的相容（`etaAnab ι S = B.val.eta (logVol (out ι S))` 的形状）。见 `obligations.csv`。
3. **更强的可选路线**（**不是**目标的一部分）：证明读数在**整个** `S` 族上不变（= W5/W7 那条）。
   它是更强的条件；把目标写成它会把问题变得不可解，且与 (9-1) 不等价。

## 5. 到 Corollary 3.12 与 abc 的依赖（单列，不预设已完成）

- (9-1) 本身是 Cor 3.12 论证里的一步，**不是** Cor 3.12 的充分条件：Cor 3.12 还需要 xi-d…xi-f 的 log-volume 计算、
  以及 Θ-link / 多radial 兼容的其余部分。
- 即使 (9-1) 成立，到 `abc` 还需要把 Cor 3.12 的算术结论接到数域上的 height 比较，并处理 `q`-pilot 的算术来源。
- 本清单**不**声称上述任一步已具备；它们各自是独立的缺口（见 `obligations.csv` 的 dependency 行）。

## 6. 什么不算完成

- 在玩具模型里证出「ℝ→ₗ[ℝ]」版本（W11）不算；(9-1) 的 `R^val,R^ss` 来自 `out`、`BPS`、`Ind3`、`logVol`，玩具里没有这些对象。
- 证出「存在 `ι,S` 使某标量关系成立」但没有把 `S` 落到 `Ind3 D` 的真实元素上，也不算。
- 静态地指出「原文这么写」不算证明；反过来，把原文的一句话当成"已证"同样不算。
