# 当前路径（2026-10-23，随 W7 交付一并记录）

本文件说明**我正在走的这条路径**：它从哪里来、现在到哪、下一步往哪。它记录的是**研究方法与产物位置**，
不是数学结论；任何"已证/未证"都以对应目录下的 `delivery.json` 与源码为准。

## 这条路径的形状

一句话：**先把原文的接线点定位清楚，再把"读数必须落在对象上、而不是落在呈现上"这条纪律逐层做成 Lean 类型，
每一步都用 CLI + 公理白名单 + 编辑器零诊断三关验收。**

所以它不是"往前推 IUT 的某个定理"，而是**先建可检验的接口**：把 H1（原文环境范畴与商层级）、H3（归一化记账）、
K4（执行来源）这三处最容易含糊的地方，各自做成一个能编译、能审计、能被反例打脸的小省份。

## 已经走过的（按时间顺序，均可按提交回溯）

| 步 | 产物 | 它确立了什麼 | 提交 |
|---|---|---|---|
| M1–M4 静态 | `handoffs/core-backward-2026-10-23/M{1,2,3,4}/` | 原文箭头/端点清单、归一化账本、11 个接口的字段与"是否显式要求执行/degree"、可复用构造清单 | `24396d8`、`2718711` |
| H1 | `research/core-backward-2026-10-23/h1-decision.md`、`h1-coricity.md` | 环境范畴是 `F⊩▶×μ-prime-strips`（原文声明过）；商是**两层**（`⊼fQ₁` 的集合层 orbit 与 `⊼fQ₂ modulo ⊼fQ₁` 的形式商）；`(n,◦)` 是由纵线"determined up to isomorphism"的单对象；vertical coricity 给 **full poly-isomorphism**（= 同构轨道），而诱导到 prime-strip 层**不是 full** | `ca9428e`、`4f80a1c`、`6cb80fb` |
| K4 | `candidates/core-transport/ExecutionProvenance.lean` | 把"合法执行"做成**类型级**要求：轨迹按定义等于算法（`steps_eq`），值由收敛＋唯一性**推出**，而 `realisation` 只是落点条件 | `0babeb9` |
| W1 | `candidates/core-transport/ReadingInvariance.lean` | 呈现可换、读数不变；**部分读数不具**此不变性（具体反例） | `b011762` |
| W2 | `candidates/core-transport/CollectionProvenance.lean` | provenance 抬到 local-global collection；落点条件不足以决定全局读数 | `3e257dc` |
| W3 | `candidates/core-transport/DivideBackLaw.lean` + `h3-prerequisites.md` | 玩具层"除回 M 次幂"法则；范数读数**失败**；H3 三条账面义务带定位 | `3e257dc`、`3dcff73`、`16837a4` |
| IUT II | `research/round2-source-cache/iut-II-…{pdf,txt}` | 补上对齐所缺的来源：Cor 4.10(i) 的 `0 ↔ ⟨F_l^⋆⟩` 认同**存在** | `8a6ada4` |
| W4 | `candidates/core-transport/TransitionCompatibility.lean` | 带余圈律的过渡；相容链迫使读数相同，断裂链不 | `8a6ada4` |
| W5 | `candidates/core-transport/NormalizationAlignment.lean` | 不变读数 ⇒ **轨道平均 = 标签处取值**（`0 ↔ ⟨F_l^⋆⟩` 的代数内容） | `ae9d90d` |
| W6 | `candidates/core-transport/ReadingFactorization.lean` | 读数**下降到商**（`Quotient.lift`）；断裂链上**没有**因子化 | `ae9d90d` |
| W7 | `candidates/core-transport/UnifiedFactorization.lean` | W5 的群轨道与 W6 的过渡关系合成**一条**：两条关系上的常数性 ⇒ 并上常数性 ⇒ 读数下降到并商；W5/W6 还原为调用同一 `descended` 的实例 | `bf859ae` |
| M-i | `candidates/core-transport/DivideBackTwist.lean` + `research/…/m-i-design.md` | 除回活在**读数层**；twist 项 `τ` 显式写出，不变性 ⟺ `τ = 0`；并**证出** `‖localLog 4‖ = 1/3`，故 `τ ≠ 0` 有具体见证 | `cfd3796`、`ed39245` |
| M-ii | `candidates/core-transport/ExponentUniqueness.lean` + `research/…/m-ii-design.md` | 指数 `M` 被确定 ⟺ **探针读数非零**；挠探针（`x = 1`）对任意指数给相同读数 | `db181de`、`ba78ff1` |

| W10 | `candidates/core-transport/H3Synthesis.lean` | M-i 与 M-ii 是同一条同态事实的推论：`reading(x^M) = M • reading x`；非挠探针定指数；twist-free ⟺ 读数不变；两条一起给出除回；两侧退化见证（`Multiplicative ℤ` 上） | `64126ef` |

## 现在正在走的

**下一步（未开始）：把 W7 升级为"同构在轨道上相等"**，并按 LANA 报告的 (9-1) 对齐——仓库里已有
`Iut/Wall/EtaAlg.lean:151` 的 `etaAnab_eq_etaQ_iff` 作为具名等价（其 docstring 自标 "(9-1)"），所以玩具层要做的是
"两族同构 + 存在 `S` 使二者相等"的**形状**，而不是发明新接口。玩具里没有 `out`/`BPS`/`Ind3`，故不得声称触及
`etaAnab`/`etaQ`。

## 外部来源：LANA 中期报告（2026-07，已归档）

`research/round2-source-cache/LANA-interim-report-2026-07.{pdf,txt,json}`（PDF sha256 `a368345c…`）＋
评估笔记 `research/core-backward-2026-10-23/lana-report-assessment.md`。

它把我们的问题**精确命名**为 (9-1)：两条同构 `η_q : R^val ≅→ R^ss`（q-pilot 侧）与
`η_anab_S : R^val ≅→ R^ss`（anabelian/Kummer 侧，依赖所选 `S ⊂ VC(I_v)`），要证存在 `S` 使
**`η_q = η_anab_S`**；而报告自陈 "we, the LANA project, **do not have a proof of (9-1)** at this time"。

三条对我们有直接后果：

1. `R^ss` 被定义为 `{T | adelic, measurable}/∼`、`T ∼ T'` **iff 体积相等**——即报告所用的粗化商就是
   "按读数取等"的商，印证 `h1-decision.md` 的"coarse 影子"分层。
2. (9-1) 断言的是**两条同构本身相等**（在"计算 degree 之前"比较，txt 2236–2239），比我们 W5/W7 证的
   "读数沿轨道不变"**更强**：W5/W7 是**必要条件**，不是充分条件。
3. Ind1/Ind2 的歧义落在 **`S` 的选择**（txt 2267），不是落在实数上；Ind3 来自沿 log 序列**只有 upper
   semi**（Step 9，txt 2109–2116）。这给 M-iii 的对齐一个明确载体：`|F_l|` 索引 vs procession 平均，本质是
   比较两个 `S` 上的归一化。

## 下一步（已排定，按 LANA (9-1) 重新排序）

1. **把 W7 升级一档**：从"读数在并商上良定义"升级为"**两个同构在轨道上相等**"——在玩具里构造 `η_q` 与
   `η_anab_S` 两族同构，证明"存在 `S` 使二者相等"在**可证条件下**成立，并给出条件失效的见证。这是 (9-1)
   的最小忠实形状，仍在 `ℚ_[3]` 玩具层内可做。
2. **M-iii 的落地**：按 IUT II Cor 4.10(i) 的认同，把 (xi-d) 的 `|F_l|` 索引对齐到 procession 归一化。
3. **三处 `M` 的同一性**：需要 `det^{⊗M}` 的真实对象层与 `(Ob4-1)` 的 degree-M Frobenius——**超出玩具层**。
4. 只有 1–3 有结论后，才谈得上"native 读数 = 输出读数"这类陈述；(9-1) 本身**不**由本路径的任何一步给出。

## 玩具层的边界（重要）

到 W10 为止，所有 Lean 产物都在**玩具层**：读数取 `localLog`、对象取 `ℚ_[3]` 的元素、张量幂取 `x^M`。
它们把三条 H3 义务的**形状**做成可证、可审计、可被反例打脸的东西；**没有**任何一条构造了真实的
`det^{⊗M}` 对象、log-shell、prime-strip 或 Θ-link。再往上一层需要这些真实对象，属新的一层工作。

## 纪律（每一步都检查这三条）

1. **结论不进类型**：`vQ = q₀`、`vOut ≤ B` 只能是被证的定理，不得作字段。
2. **不从 hull 反推原区域**：`InHullOfImage` 只是落点方向。
3. **不用标量相等冒充来源相等**：iQ5 之后只剩数值，相同数值反推不出同一 prime-strip 见证。

以及：每一步都跑**三关**（`lake env lean -DwarningAsError=true` 零诊断 / 公理 ⊆
`{propext, Classical.choice, Quot.sound}` / 编辑器 0 error、0 warning），并把"未做/未读/属推断"的地方写清。
核心 GAP 全程 **OPEN**，未入 fact-tree。
