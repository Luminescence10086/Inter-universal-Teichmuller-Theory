# N11 — 跨领域方法迁移与工具设计

状态：`EXPERIMENTAL`（两张设计卡 + 6 次有界检索 + 一个跑通的有限模型；**卡是方案，不是结果**，推导全部 `UNVERIFIED_MATH`）。

选两条路线（另两条为什么不做见 `tool-cards.md` §0）：
- **路线 3 → 卡 1「T3-LAT 容器–最小 hull 审计器」**：仓库的 `hull` 逐字是 `scaledIntegral b` ＝ `b·O`，
  "是不是最小 hull / 有限模拉回是不是只是容器"逐字是格的饱和问题——可算、可否证。填补 **N08-G2/G3**。
- **路线 4 → 卡 2「T4-ATT 达到–证书二分器」**：`realisation` 只给**包含**（`EtaAlg.lean:123-125`），
  目标是**等式**（`EtaAlg.lean:151`）。填补 **N07-H1 / N03-O1**，并对 N07-H2 给否定性服务。

本轮唯一的实质进展（`SOURCE_FACT`）：**N08-G2 被切成两半**。
- LANA §5.2(d)（`txt:1338–1340`）把 `S^hol` 定义成"含 `S` 的**最小 `VC(O)`-子模**"，而 `VC(O) = ∏_v LocVC(O)_v`（`txt:1333–1337`）⇒ 逐坐标 `b·O`。**仓库的 `scaledIntegral b` 忠实实现了模 hull，这半边答案是"是"。**
- 未决的是 §8.1(f)（`txt:1923–1927`）"w.r.t. the ring structure at (1,1)" 的**环 hull**：环乘法耦合 tensor 因子 ⇒ 环 hull ⊆ 模 hull，一般严格更小。这一条不是检索来的，是读本地原文来的。

两张卡各自最硬的一句话：
- **卡 1**：指数集一旦不是 box，逐坐标 box 严格大于耦合闭包；有限例里后者测度 0、甚至不是 admissible 区
  （`toy_check.py` Part A，A2/A3 各给显式分离泛函）。
- **卡 2**：两个对象可以在**每个已声明字段**上一致，却一个达到目标值、一个不达到（Part B 的 M1/M2）
  ⇒ 只凭 `(T1)–(T3)` 的答案是 `UNDETERMINED`；要判定必须多声明 `sup` 那一项。

依赖：卡 2 的有效性**以卡 1 的归约（A3）为条件**（`Ind3` 不是多面体，Farkas 只在指数坐标归约后可用）。不许单独引用卡 2。

先前工作（`prior-art.md`，6 次查询用尽）：Reinhardt/对数凸包、Farkas、`p`-adic 饱和在**来源侧**都是标准理论；
**应用侧**（接到 `VC(I)`/`Ind3`/log-volume）在检索范围内无先例。**没检索到 ≠ 存在/原创**；只到标题级片段。

目录内冲突已处理：另一 agent 遗留的检索记录原样保留为 `prior-art.sibling-agent.md`（其查询对应路线 1/2，与本卡不符）；
其生成器 `make_N11_delivery.py` 改名 `.retired`（否则会静默覆盖 SUMMARY/delivery.json）。两 agent 合计查询 12 次，
超出 ≤6 的约束，已记入 `delivery.json`。

未做：环 hull 的半群闭包模型、N08-G4、N06-`O6` 归一化对齐、任何 Lean/编辑器动作。
