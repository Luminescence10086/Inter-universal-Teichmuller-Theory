# N11 先前工作检索（有界，6 次查询，2026-10-23）

用途：检查两张工具卡的两条路线（路线 3「非阿几何/格/有限模」、路线 4「约束求解与优化对偶」）是否已有现成工作
可直接搬用。**没检索到 ≠ 不存在**；这也**不**是原创性证明。检索词为英文，可能漏掉日文文献与未索引预印本。

| # | 查询 | 命中 | 与两张卡的关系 | 结论 |
|---|---|---|---|---|
| 1 | groupoid descent obstruction compatible choices anabelian reconstruction | Fantechi 讲义 *Stacks for everybody*（群胚纤维/下降的形式化）；一篇 descent spectral sequence 讲义 | 只与"路线 1（下降）"有关，而路线 1 **本轮未选**（理由见 `tool-cards.md` §0） | 不直接可用 |
| 2 | compactness theorem finite satisfiability p-adic lattices common container | Conrad, *Compactness of V/L for p-adic V*（`L` 紧、`V/L` 离散）；profinite completion 笔记 | 与"路线 2（紧致性）"有关，路线 2 **本轮未选** | 不直接可用 |
| 3 | inverse limit profinite completion lattice hull log-volume p-adic | Hoshi 讲义（profinite/单远阿贝尔几何）；RIMS Kokyuroku 讲义 | 提供卡 1 背景工具（`ℤ_p`-格、profinite），**没有**"hull = 逐坐标 box"的现成定理 | 背景可用，主结论无 |
| 4 | descent theory Galois group action compatible section existence | 群作用"截面存在"讲义 | 与卡 1 的"截面存在"同型，但仍在路线 1 框架内 | 不直接可用 |
| 5 | finite satisfiability compactness existence of common lattice over p-adic field | Conrad（同 #2） | 无新命中 | 无 |
| 6 | anabelian reconstruction mono-anabelian group-theoretic algorithm Hoshi | Hoshi, *Introduction to mono-anabelian geometry*（已在 LANA 参考文献 [1] 中） | 给卡 1 的"重建侧"标准工具，但**不**解决 `out` 的构造（N07-H1） | 背景可用，主结论无 |

## 结论（三条）
1. **卡 1 的核心判据没有被检索到现成结论**：把 hull 审计化归为"指数集是不是 box / 是否饱和"（卡 1 §1.4）在有限模型里可算，
   但检索未命中任何"已证明原始 hull 恰为逐坐标 `λ·O`"的工作——这与 N08 的 G2 仍然 OPEN 一致。
2. **卡 2 的三值分类器同样没有现成实现**：Farkas/对偶是标准工具，但"在 `Ind3` 的读数像上把'达到'与'上界证书'分开"
   未见现成表述；仓库侧最接近的是 `Constraints.lean:201` 的"log-vol 形状 ⇒ S–S 不等式"。
3. **路线 1、2 被排除不是因为检索到反例，而是因为在本工程里它们要先造缺失的结构**（群胚态射的 `τ` 公式、`Region D` 上的拓扑），
   这与检索无关（见 `tool-cards.md` §0）。

## 检索的边界
- 6 次查询全部为英文关键词，未检索日文文献与 IUT 相关讨论班材料。
- 未检索 arXiv 全文，只看了搜索引擎返回的摘要级片段；任何"未见"都不排除存在。
