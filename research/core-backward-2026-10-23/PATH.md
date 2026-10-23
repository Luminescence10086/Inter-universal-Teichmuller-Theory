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

## 现在正在走的

**W7 — `candidates/core-transport/UnifiedFactorization.lean`（进行中）**：把 W5 的"群轨道不变"与 W6 的"过渡关系
下降"合成**一条**陈述——两条关系 `R`（过渡生成）、`S`（群作用生成）各自的不变性 ⇒ 在它们的**并**上不变 ⇒
读数通过 `Quotient.lift` 下降到并商，并把 W5、W6 还原为它的两个实例。若这次合成成功，前面两个文件就不再是两个
特例，而是同一个纪律的两次落地。

## 下一步（已排定，尚未开始）

1. **M-i 的类型设计**：原文 (Ob4)/(Ob4-3) 只**断言**"除回 M 次 tensor power 无害"，既无映射也无界。W3 给了
   "除以标量 M"的玩具；真实形状需要**一个把 M 次幂读数送回原读数的具名操作**，并证明它与 twist 不定性相容。
   这是三条 H3 义务里最难的一条。
2. **M-ii**：证明三处 `M` 是同一个（hull 的 `det^{⊗M}`、q-pilot 侧的 M 次幂、`(Ob4-1)` 的 degree-M Frobenius）。
   三者若不同，(Ob4) 的"无害"不自动成立。
3. **M-iii 的落地**：按 IUT II Cor 4.10(i) 的认同，把 (xi-d) 的 `|F_l|` 索引**对齐**到 procession 归一化——
   现在这已从"缺来源"降级为"引用在手的认同做定义对齐"。
4. 只有 1–3 有结论后，才谈得上"native 读数 = 输出读数"这类陈述。

## 纪律（每一步都检查这三条）

1. **结论不进类型**：`vQ = q₀`、`vOut ≤ B` 只能是被证的定理，不得作字段。
2. **不从 hull 反推原区域**：`InHullOfImage` 只是落点方向。
3. **不用标量相等冒充来源相等**：iQ5 之后只剩数值，相同数值反推不出同一 prime-strip 见证。

以及：每一步都跑**三关**（`lake env lean -DwarningAsError=true` 零诊断 / 公理 ⊆
`{propext, Classical.choice, Quot.sound}` / 编辑器 0 error、0 warning），并把"未做/未读/属推断"的地方写清。
核心 GAP 全程 **OPEN**，未入 fact-tree。
