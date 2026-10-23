# LANA 中期报告评估：它把我们的问题精确命名了，并抬高了门槛

日期：2026-10-23。来源：**Project LANA Interim Report on IUT Theory**（2026-07），50 页。
归档：`research/round2-source-cache/LANA-interim-report-2026-07.{pdf,txt}`
（PDF sha256 `a368345c1b4f03d9dba439cee7d3b186465b802233392b1fc7727edec8be2f30`，640,457 B；
文本化 txt sha256 `5fc6185d6642e70ba58c6ce637ef6e0448e2761b9d57b5e40545aea3d6ee040e`，用 `pypdf` 抽取，50 页标记）。
配套：`https://github.com/lana-agents/iut`（`Inter-universal Teichmüller theory: the ABC/IUT trunk.`，默认分支 `main`，Lean）。
本文件只做**来源评估与路径含义**，不是数学结论。

## 1. 报告说了什么（要点，均带定位）

- 报告主题就是 **Thm 3.11 → Cor 3.12** 的过渡，覆盖 initial Θ-data、Hodge theaters、prime-strips、log-shells、
  volume containers、Θ-link、multiradial algorithm（目录 pp.1–9 的节标题）。
- **摘要**（p.1）：报告"isolate a specific compatibility problem at the final stage"，并明确
  "Project LANA has **not yet reconstructed a proof** of the required compatibility"，因此
  "does not offer a final verdict on the validity of IUT theory"。
- **主要目标 (9-1)**（txt 2117–2141，§9.2，pp.45–46）：两条同构
  `η_q : R^val ≅→ R^ss`（由 q-pilot 与 q-side 的 native arithmetic holomorphic structure 给出）与
  `η_anab_S : R^val ≅→ R^ss`（由 anabelian/Kummer 方法、并选定 integral structure `S ⊂ VC(I_v)` 给出），
  要证存在合适的 `S` 使 **`η_q = η_anab_S`**。
- **§9.3**（txt 2142–2157）：`R^val` 来自 value-group portion（带 canonical pilot）；`R^ss` 来自
  unit monoid → log → log-shells → volume containers 的构造；`η` 描述两者关系；(9-1) 断言 `η_q` 落在
  `η_anab_S` 的**轨道**里（"an analogue of a Teichmüller deformation"）。
- **Step 9**（txt 2109–2116）：比较 log-shells 时"Along the log sequence this comparison is **only upper
  semi-compatible**. Hence … one can read the output in terms of the original input data in the log-shells
  `étI_{v,t}` with **Ind3-ambiguity**."
- **§10.5 暂定评估**（txt 2274–2289）：与 Scholze–Stix 一致同意 Figure 7 的图**不交换**；但认为 S–S 把构造压扁了，
  且 (9-1) "not manifestly false"；**"however, we, the LANA project, do not have a proof of (9-1) at this
  time."**
- **§10.3–10.4**（txt 2230–2273）：S–S 试图把 Θ-link 两侧的 `R` 副本认同以取得"共同地面"，而原文的 Θ-link
  **不是**用于直接比较两侧数值；Ind1/Ind2/Ind3 的作用是制造 `S` 的**选择歧义**，不是直接作用于实数。

## 2. 与我们在做的工作的对应（这一节是重点）

| 我们的产物 | 报告里的对应物 | 关系 |
|---|---|---|
| `h1-decision.md` 的"两层商" | `R^ss = {T ⊂ VC(I_v) ‖ adelic, measurable}/∼`，`T ∼ T'` **iff 体积相等** | **印证**：报告的粗化商就是"按读数（体积）取等"的商，正是我说的 coarse 影子 |
| W5/W7 的"读数沿轨道不变 ⇒ 下降到商" | (9-1) 说 `η_q` 落在 `η_anab_S` 的**轨道**里 | **同形状**，但报告的断言更强（见下） |
| W1 的"呈现可换、读数不变" | `η_anab_S` **依赖 `S`**；Ind1/Ind2 造成 `S` 的选择歧义 | **印证**：不变性要沿 `S` 的选择 |
| M-iii 的"归一化对齐" | `R^ss` 上的 **normalized log-volumes**；procession 归一化 | 一致：读数是在 `R^ss` 上比较的 |
| W6 的"断裂链上没有因子化" | Step 9：沿 log 序列**只有 upper semi**，Ind3 只能给上界 | **印证**：Ind3 把等式降为上界 |

## 3. 它改变了什么（对我们下一步的实质影响）

1. **门槛被抬高，但我先前把关系写错了（已改）**：我们的玩具证的是"**读数**沿轨道不变 ⇒ 读数下降"；而 (9-1)
   断言的是**两条同构本身相等**（`η_q = η_anab_S`），即在"计算 degree 之前"比较两个构造（报告 2236–2239 明说
   "before computing degrees"）。**但 (9-1) 只要求存在一个 `S`**，并不要求读数沿整个选择族不变。
   `research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean` 给出严格反例
   （`existence_does_not_force_invariance`：存在 `b` 使 `candidate b = target`，并不蕴含读数对整个 `b` 族不变），
   所以 **W5/W7 的"沿轨道不变"不是 (9-1) 的必要条件**——它们是**不同的、更强的族条件**。此前写成"必要条件"
   是错的，此处更正。下一步的玩具若要贴近 (9-1)，应做的是"存在 `S` 使两条映射相等"，而不是"沿族不变"。
2. **`S` 是真正的自由变量**：Ind1/Ind2 的歧义落在 `S ⊂ VC(I_v)`（报告 2267），而不是落在实数上。这给 M-iii
   的对齐一个明确载体：`|F_l|` 索引与 procession 平均的对齐，本质上是在比较两个 `S` 上的归一化。
3. **一个独立、专业来源确认了缺口**：并非只有我们读不懂——LANA 自己也说没证出 (9-1)。这对我方纪律的含义是：
   **不得把 (9-1) 当已知**，也不得把"我方能证的玩具形状"当作它的替代。
4. **对 S–S 的定位要更细**：报告同意 Figure 7 不交换，但认为 (9-1) 未必假；两者共识是"问题都在 **R 的副本认同**"。
   这与我们 `h1-coricity.md` 的"轨道不是 full"是同一类问题的不同侧面。

## 4. 因此下一步（写进 PATH）

- 把 W7 的玩具**升级一档**：从"读数在并商上良定义"升级为"**两个同构在轨道上相等**"——即在玩具里构造
  `η_q` 与 `η_anab_S` 两族同构，证明"存在 `S` 使二者相等"在**可证条件下**成立，并给出条件失效的见证。
  这是 (9-1) 的最小忠实形状，且仍然完全在 `ℚ_[3]` 玩具层内可做。
- 仍不做的：不声称 (9-1) 成立；不把 `R^ss` 的"体积相等商"当成 (9-1) 的替代；核心 GAP 保持 OPEN。

## 5b. 仓库比对（`lana-agents/iut`，2026-10-23 克隆）

经用户允许，把 `https://github.com/lana-agents/iut` 克隆到
`reviews/core-round/external/lana-agents--iut`（**未入 Git**：`reviews/core-round/external/` 下的外部仓库本来
就都不受版本控制，只以清单记录 commit）。克隆 HEAD `188ff572b61b748e5606d1419980f1e0b5abb0aa`，7.37 MB。

**与被审版本的关系**：本仓库与我们一直审的 `external/iut`（commit `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`）
是**同一个仓库**。

- **新增 6 个 Lean 文件**（424 → 430）：`Iut/Reconstruction/Cusp/{BelyiSpec,Cor37c,SurfaceGeom,SurfacePi1}.lean`
  与 `Iut/Reconstruction/Thm19/{CuspPrincipal,NFKummer}.lean`；
- **既有 Lean 文件另有 5 处修改**：`Iut.lean`、`Iut/Anabelian/Tempered.lean`、
  `Iut/Anabelian/TemperedAndre.lean`、`Iut/Reconstruction/Cusp/Belyi.lean`、
  `Iut/Reconstruction/Cusp/Elliptic.lean`。**先前我只比了 7 个接口就写"其余逐字节相同"，这是错的**；
  准确结论是"**我们 M3 审过的这 7 个文件在两版间逐字节相同**"，不等于整棵树未变。另有三类非 Lean 变更
  （`lakefile.toml`、`lake-manifest.json`、`scripts/shell_lint_allowlist.txt`）与三份文档变更
  （`AutHolomorphic/README.md`、`Multiradial/ROADMAP.md`、`Plans/MR9Plan.md`），以及新增的 `Plans/MR10Plan.md`；
- 我们 M3 审过的 7 个文件（`Wall/EtaAlg`、`Wall/Constraints`、`Wall/Ind3`、`Wall/Rss`、`Wall/MultiContainer`、
  `LogLink/Kummer`、`LogLink/Thm311LGP`）**逐字节相同** ⇒ **M3 的接口结论对固定 commit 仍然有效**，
  不因上游前进而失效（但不蕴涵"整棵树未变"）。

**README 的自我定位（重要）**：「It does **not** verify IUT.」主定理是
`Iut.classicalABC_of_variant (h312 : Cor312VariantHolds) : ClassicalABC`——即 ABC 是**从变体**推出的，
而 `Cor312VariantHolds` 是 project-owner 指定的 **Cor 3.12 variant**（含 initial Θ-data、log-shell 的
processions/tensor-packets、large volume container、其 log-volume、holomorphic hull）。

**最关键的发现：这份仓库里 (9-1) 已经被形式化了**，而且正是 M3 读到的那条接口：

- `Iut/Wall/Rss.lean:501`：`noncomputable def etaQ : (qVal D.bpsDegrees).C →ₗ[ℝ] ℝ`（`η_q` 是**定义**）；
- `Iut/Wall/EtaAlg.lean:145`：`noncomputable def etaAnab …`（`η_anab` 也是**定义**）；
- `Iut/Wall/EtaAlg.lean:151`：`theorem etaAnab_eq_etaQ_iff (ι S) : A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs`
  其 docstring 逐字写着：「`etaAnab_eq_etaQ_iff`: **(9-1)** for `(ι, S)` holds iff `log-vol(out ι S) = −|log q|`:
  an equation between two maps of pointed lines *is* an equation of real numbers」。

  也就是说：**报告的 (9-1) 在仓库里等价于一条标量 log-volume 等式**——但这条等价是在**模型内**成立的，
  而模型里的 `out` 是裸字段（M3：11 个接口 F3 全 false，没有执行来源）。所以它是 (9-1) 的**模型内改写**，
  不是对真实算法的证明。

**另一条对我们极有用的文件：`Iut/WallEquiv/NonDerivable.lean`**，标题即
**「Non-derivability of Step (xi) from Theorem 3.11」**：

- `theorem xi_iff : P.Xi ↔ P.SS`（`Iut/WallEquiv/NonDerivable.lean:273`）——在 `Thm311Package` 抽象里，
  **Step (xi) 等价于 Scholze–Stix 不等式** `(s − 1)·a ≤ V`；
- `not_xi_family` / `exists_package_not_xi` / `not_forall_xi`——对一切与已证数字相容的取值，以及显式地
  `ℓ = 7, a = 1, V = 1`（此时 `(s − 1)·a = 11/3 > V`），存在 package 使其**全部字段成立而 Step (xi) 失败**，
  故**只用这些字段的任何论证都证不出 Step (xi)**；
- 文件自己标注了边界：「**Audited, not a theorem**: that these fields exhaust what the repository proves at
  the level of Theorem 3.11」。

**这对我们意味着三条**：

1. (9-1) 不需要我们自己发明——它是仓库里一条具名等价（`etaAnab_eq_etaQ_iff`）；我们 M3 读到的正是它。
2. 仓库把 (9-1) 化成**标量**等式；我们对"标量相等 ≠ 来源相等"的纪律仍然适用，但要表述准确：**模型内**二者
   等价（有定理），**模型外**（真实算法）仍未证。
3. `NonDerivable` 是上游给出的、Lean 检查过的"缺口不可由 Thm 3.11 字段关闭"的陈词——与报告 §9.2/§10.5 一致，
   且同样带"审计而非定理"的自我限定。

## 5b′. 逐字引用（W11 的对齐锚点）

以下三处是 W11（玩具层的 (9-1) 形状）应当对齐的**真实陈述**。注意 docstring 自己写明它们形式化的是
**[LANA] §9.2**，也就是报告 §9.2 的那两条映射。

`Iut/Wall/EtaAlg.lean:143–149`：

```lean
/-- **`η^anab_{ι,S} : R_val → R_ss ≅ ℝ`** ([LANA], §9.2): the pointed map sending the pilot of
the input to the class (log-volume) of `M = 1·S`, the output `out ι S`. -/
noncomputable def etaAnab {B : A.BPSA} {h : A.Side} (ι : A.Choice B h) (S : Ind3 D) :
    B.val.C →ₗ[ℝ] ℝ :=
  B.val.eta (logVol D (A.out ι S))
```

`Iut/Wall/EtaAlg.lean:151–153`（证明只用了 `ValBPS.eta_eq_eta_iff`）：

```lean
theorem etaAnab_eq_etaQ_iff {h₁ h₂ : A.Side} (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D) :
    A.etaAnab ι S = etaQ D ↔ logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs
```

`Iut/Wall/Rss.lean:498–501`：

```lean
/-- **The map `η_q : R_val → R_ss`** ([LANA], §9.2) … It is an isomorphism of pointed real lines
(`etaQ_bijective`). -/
noncomputable def etaQ : (qVal D.bpsDegrees).C →ₗ[ℝ] ℝ :=
  (qVal D.bpsDegrees).eta D.qPilot.lhs
```

**由此确认三件事**：(i) 报告 §9.2 与仓库接口是**同一兼容性目标的模型化接口，忠实性尚未证明**；(ii) 仓库把 (9-1) 归约成标量等式
（`etaAnab_eq_etaQ_iff`），其引理 `ValBPS.eta_eq_eta_iff` 就是"点线映射相等 ⟺ pilot 处取值相等"——W11 要证的
正是这条引理的抽象版；(iii) 两个映射都形如 `η = (·).eta (标量)`，即**由一个标量决定**，所以 (9-1) 在该模型里
必然是标量等式，`out` 的裸字段性（M3 F3）决定了这是模型内归约。

## 5c. 由此对路径的调整

- 我们不再需要自己构造 η 的形状（那是重复劳动）：W7 的"同构在轨道上相等"可以**直接对齐**
  `etaAnab_eq_etaQ_iff` 的两边，做的是"玩具层面的同构相等"而非发明新接口；
- 但**不能**声称我们的玩具触及 `etaAnab`/`etaQ`：它们依赖 `out`、`BPS`、`Ind3` 等真实模型对象，
  在 `ℚ_[3]` 玩具层里没有对应物；
- `NonDerivable` 的 `xi_iff` 给了我们一条可引用的"必要条件"表述：若某步只使用 Thm 3.11 的字段，
  它不足以得到 Step (xi)。

## 6. 两页 ZEN 公告

`zen.ac.jp/news/zmcpostevent0331e`（2026-03-31：宣布 LANA 项目启动）与 `…0717e`（2026-07-17：发布本中期报告）
只提供项目背景与报告发布信息；正文被 `web_fetch` 截断（只取到标题），**本文件的内容全部来自上面归档的 PDF
与克隆的仓库源码**，不是从这两个页面转述的。
