# LANA 中期报告评估：它把我们的问题精确命名了，并抬高了门槛

日期：2026-10-23。来源：**Project LANA Interim Report on IUT Theory**（2026-07），50 页。
归档：`research/round2-source-cache/LANA-interim-report-2026-07.{pdf,txt}`
（PDF sha256 `a368345c1b4f03d9dba439cee7d3b186465b802233392b1fc7727edec8be2f30`，640,457 B；
文本化 txt sha256 `5fc6185d6642e70ba58c6ce637ef6e0448e2761b9d57b5e40545aea3d6ee040e`，用 `pypdf` 抽取，54 页标记）。
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

1. **门槛被抬高**：我们的玩具证的是"**读数**沿轨道不变 ⇒ 读数下降";而 (9-1) 断言的是**两条同构本身相等**
   （`η_q = η_anab_S`），即在"计算 degree 之前"比较两个构造（报告 2236–2239 明说 "before computing degrees"）。
   所以 W5/W7 是**必要条件**，不是充分条件。下一步的玩具应当从"读数值不变"升级为"**同构在轨道上相等**"。
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

## 5. 两页 ZEN 公告

`zen.ac.jp/news/zmcpostevent0331e`（2026-03-31：宣布 LANA 项目启动）与 `…0717e`（2026-07-17：发布本中期报告）
只提供项目背景与报告发布信息；正文被 `web_fetch` 截断（只取到标题），**本文件的内容全部来自上面归档的 PDF**，
不是从这两个页面转述的。
