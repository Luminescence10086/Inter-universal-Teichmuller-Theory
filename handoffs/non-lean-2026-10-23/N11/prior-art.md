# N11 — 有界先前工作检索（6 次查询，上限用尽）

日期：2026-10-23。检索工具：`web_search`。**总查询数 = 6（契约上限）**，此后未再检索。

> **目录内并行记录说明**：本目录先有一份由**另一个 agent** 写入的 `prior-art.md`，其 6 次查询全部关于
> 「路线 1 群胚/下降」「路线 2 紧致性」，与本工作包实际选定的路线 3/4 **不对应**。该文件已原样保留为
> `prior-art.sibling-agent.md`（哈希见 `delivery.json`），**不**作为本交付的检索记录采信；
> 下面这份才对应两张工具卡。两个 agent 各查 6 次（合计 12 次）这一事实本身也记在 `delivery.json` 的
> `unresolved` 里，不掩盖。

## 0. 方法与限度（先说清楚，否则"命中/未命中"会被误读）

1. `web_search` 返回的是**标题 + URL + 片段**，本轮**没有**抓取任何页面正文（未用 `web_fetch`）。
   因此"命中"= 标题/片段层面命中，**不等于**我读过该文并核实其主张。
2. 第 1–3 条 query 在**同一次调用**内提交，返回的是一个**合并**的 8 条来源列表；下表按内容做归属，
   归属本身是**我的判断**，不是接口返回的字段。
3. 没有做 Google Scholar / arXiv 全库 / MathSciNet 的系统检索，也没有时间窗过滤。
4. **未命中 ≠ 原创**。下面的"未命中"只能支持一句话："在这 6 次标题级检索的范围内没有发现"，
   **不能**支持"此前无人做过"，**更不能**作为新颖性主张。两张工具卡据此一律只标 `PROPOSED`。

## 1. 检索记录

### Q1 — `LANA interim report 2026 Mochizuki IUT eta algorithm (9-1)`（合并返回）

- **命中**：
  - `https://zen.ac.jp/zmc/topics/2c02nd0a7` —— LANA 中间报告官方页（与本地缓存
    `research/round2-source-cache/LANA-interim-report-2026-07.txt` 同一份报告的公开出处）。
  - `https://www.newscientist.com/article/2580313-effort-to-solve-biggest-controversy-in-mathematics-has-made-no-progress/`
    —— 报道性文章，标题即 "no progress"。
  - `https://zenodo.org/records/22882700/.../RIG7_RIGIDITY_PIN_AUG05.md` —— 标题直接写
    "WHY (9-1) IS STUCK WHERE LANA STANDS"。
- **未命中**：没有找到任何给出 (9-1) 证明的材料；也没有找到任何"工具/算法"形态的材料。
- **结论**：公开层面对 (9-1) 的状态与本地材料一致（**未证**）。但 zenodo 两条是**未经同行评审的灰文献**，
  作者与性质本轮未核实，**不得**当作已确立的分析引用；`RIG7` 与 `Forensic Diagnosis` 在本文件中仅作
  "有人在同方向工作"的线索登记。

### Q2 — `holomorphic hull Reinhardt domain log-convex Cartan-Thullen`（合并返回）

- **命中**（迁移来源的"来源侧"有据）：
  - `https://math.ucr.edu/~slapan/math/605_Several_Complex_Variables.pdf` —— 片段即
    `L(A) = {(log|z_1|,...,log|z_n|) ∈ ℝ^n | z ∈ A, z_i ≠ 0}`，正是把区域搬到对数坐标的那一步。
  - `https://theses.hal.science/file/index/docid/60401/filename/these2.pdf` —— 片段含
    "log-convexe si {(log|z_1|, ...)}"。
  - `https://www.mathematik.de/images/DMV/Jahresberichte/Jahresberichte_Archiv/JB_DMV_098_2.pdf` ——
    Holomorphiegebiete（Behnke / Cartan / Thullen）史述。
- **未命中**：没有任何材料把"完备 Reinhardt 域包络 = 对数凸包"接到 IUT 的 `VC(I)` / log-shell hull 上；
  也没有非阿（Berkovich / 刚性）版本的对数凸包定理被检索到。
- **结论**：卡 1 的迁移在**来源侧**是标准理论；**应用侧**（非阿 + 环结构 + IUT 容器）在检索范围内无先例。
  这支持"可以迁移"，**不支持**"这个迁移是新的"。A5 因此仍是 `PROPOSED`，须补非阿情形的引证。

### Q3 — `Mochizuki log-shell hull VC(I) Corollary 3.12 log-volume`（合并返回）

- **命中**：
  - `https://export.arxiv.org/pdf/2004.13228` / `https://ar5iv.labs.arxiv.org/html/2004.13228` —— Scholze–Stix，
    Cor 3.12 的陈述、initial Θ-data、Ind1/Ind2，片段里出现 `ℐ_{\underline v} = ℐ_{\underline v_0} ⊗ ⋯`。
  - `https://www.kurims.kyoto-u.ac.jp/~motizuki/Rpt2018.pdf` —— 片段是实数 `λ` 与 `a, b, λ` 的不等式。
  - `https://zenodo.org/records/21899747/.../IUT_Cor312_Forensic_Diagnosis_{ger,kombi}.pdf` —— 灰文献。
  - `https://ar5iv.labs.arxiv.org/html/2401.13508` —— "Construction of Arithmetic Teichmuller Spaces III …
    a proof of Mochizuki's Corollary 3.12"，片段给出 `LogVol_{L'_w}(S) = log(Vol_{L'_w}(S))`。
- **未命中**：**没有**任何材料讨论"`hull(VC(I))` 到底是逐坐标 box 还是耦合/环 hull"这个具体问题；
  也没有材料讨论"若按 box 算，容器读数是否还是 IUT IV 用的那个数"。
- **结论**：卡 1 的问题在检索范围内**未被提出过**（≠ 我第一个提出）。
  附带风险登记：`2401.13508` 声称证明 Cor 3.12。若该声称成立，wall 的地位会变。**本轮不评**（超出边界，
  且与 N02 的争议矩阵重叠），只登记为"外部竞争性声称，未审"。

### Q4 — `Farkas lemma certificate of infeasibility attainment polyhedral duality gap`（单独）

- **命中**（对偶/证书侧是教材内容）：CMU 15-859 lecture 12（Theorem 12.9）、
  `http://web.mit.edu/~jadbabai/www/ESE504/lectures.pdf`、SDU `dm545_handout_farkas.pdf` 与 `dm545-main.pdf`、
  Padova `Programmazione-Lineare-08-09.pdf`（"Inammissibilità e Lemma di Farkas"）、Stanford MS&E310 final review。
- **未命中**：没有任何材料把"上界证书 vs 达到的见证"这一二分用到 IUT 的 log-volume / 区域 / Ind3 上。
- **结论**：卡 2 的**机械部分**是标准结果（这降低"发明新数学"的风险，也降低新颖性）；
  **应用**在检索范围内无先例。Farkas 能否用在 `Ind3` 上取决于"指数坐标归约"是否成立（卡 1 的 A3），
  这一点检索完全没有覆盖——它是本地的、要靠读仓库解决，不是靠检索。

### Q5 — `p-adic lattice saturation non-archimedean holomorphic hull Z_p module`（单独）

- **命中**：
  - `http://arxiv.org/pdf/math/0612611` —— 片段："The saturation of `AlH` contains by definition the elements
    `μ z^α`, `μ ∈ ℚ_p` with `w(…)`"——说明"饱和"在非阿解析对象上确有对应概念。
  - `https://digitalcommons.usf.edu/...` —— Dirichlet 定理："`Log(O_K^×)` is a lattice of rank `r+s−1`"
    （格/体积的经典源头）。
- **未命中**：**没有** `tensorLogShell`、`LocVC(O)_v`、"最小 `VC(O)`-子模"、容器 vs 最小 hull 的任何直接讨论。
- **结论**：卡 1 的 A6（饱和 vs 整闭包）在来源侧有概念支撑，应用侧无先例。
  **注意**：`math/0612611` 我只看到片段，未读正文；"饱和"在该文里指什么**未核实**。

### Q6 — `Mochizuki IUT Ind3 indeterminacy set S subset VC(I) log-volume Corollary 3.12 xi`（单独）

- **命中**：
  - `https://zenodo.org/records/21899747/.../Forensic_Diagnosis_kombi.pdf` —— 片段：
    "im Beweis von Korollar 3.12, dass die prozessionsnormalisierten Log-Volumina 'die Unbestimmtheit (Ind3)
    in eine Ungleichung [von …]'"——即 Ind3 被化成一个**不等式**。方向与仓库
    `Constraints.lean:201`（wall ⟺ Scholze–Stix 不等式）一致。
  - `https://www.kurims.kyoto-u.ac.jp/preprint/file/RIMS1759.pdf` —— 片段含 `v_ℚ ∈ V_ℚ^{non} ∖ V_ℚ^{dst}`。
  - 以及 Q3 的 Scholze–Stix / Joshi III。
- **未命中**：**没有**"见证 / 严格证书 / 未定"这个三值形态；没有把 `realisation` 的"只给包含"当作独立缺项处理的材料。
- **结论**：卡 2 的**问题形状**（Ind3 → 不等式）在外部材料里有同方向观察（但仍是灰文献，只能作线索）；
  三值分类这个具体工具在检索范围内无先例。

## 2. 汇总表

| Q | 主题 | 命中强度 | 对本轮的作用 |
|---|---|---|---|
| 1 | (9-1) 的公开状态 | 中（官方页 + 报道 + 灰文献） | 支持"不许当已解"，**不**支持任何工具已存在 |
| 2 | Reinhardt 域 / 对数凸包 | 强（教材级） | 卡 1 迁移的**来源侧**有据；应用侧无先例 |
| 3 | Cor 3.12 / hull / log-volume | 中（Scholze–Stix、望月、Joshi） | 卡 1 的问题未被提出过；登记 Joshi 的竞争性声称（未审） |
| 4 | Farkas / 达到 vs 证书 | 强（教材级） | 卡 2 的机械部分标准；应用无先例 |
| 5 | `p`-adic 饱和 / 格 | 中（片段） | A6 概念有支撑；未核实正文 |
| 6 | Ind3 → 不等式 | 中（灰文献） | 与 `Constraints.lean:201` 同方向；三值形态无先例 |

## 3. 因为读到了东西而**改动**设计的两处（可复核）

1. **本地原文（不是检索）改掉了卡 1 的靶子**：初稿把"hull = 逐坐标 `λ·O` 还是对数凸包"当成一个未定对比。
   读到 `LANA-interim-report-2026-07.txt:1338–1340` 后改为：**模 hull 由 §5.2(d) 定义死**
   （含 `S` 的最小 `VC(O)`-子模 ⇒ 逐坐标 `b·O`，因为 `VC(O) = ∏_v LocVC(O)_v`，`txt:1333–1337`），
   未决的是 §8.1(f)（`txt:1923–1927`）"w.r.t. the ring structure at (1,1)" 的**环 hull**。
   → 记法：**这次"检索没找到"确实只是"没找到"**，补证来自读原文，不是来自搜索。这一条恰好演示了
   "把没检索到当原创"会怎样出错。
2. **Q3 的 Joshi 声称**：登记为外部竞争性声称并**不做评价**。若将来采纳，卡 2 的 F1（"分类恒为同一类 ⇒ 撤回"）
   会提前触发。这一点写进 `delivery.json` 的 `unresolved`。

## 4. 若允许更多查询，下一步该查什么（本轮不做）

1. arXiv 全文检索：`"holomorphic hull" AND "log-shell"`；`"smallest VC(O)-submodule"`。
2. 本地 `research/round2-source-cache/` 里 IUT I–IV 的 txt 直接 grep `hull`（**不需要网络**，成本最低，优先）。
3. Berkovich / 刚性解析空间上的"对数凸包 / Reinhardt 域包络"定理（补 A5 的非阿引证）。
4. 望月对 Scholze–Stix 的直接回应（补 N02 的争议项，本任务不需要）。

## 5. 目录内的第二份检索记录（不采信，保留备查）

`prior-art.sibling-agent.md`：由并行 agent 写入，6 次查询均为
`groupoid descent obstruction … / compactness theorem finite satisfiability … / inverse limit profinite …` 等，
对应**未选定**的路线 1、2。它对卡 1/卡 2 的主结论给出的结论是"不直接可用 / 背景可用，主结论无"，
与本次检索的结论方向一致（都未命中现成工作），但**不对应**所选路线，故不作为本交付的检索记录。
两份额外的证据代价：本任务因此实际发生了 **12 次**查询，超出"≤6 次"的约束；这一点不隐瞒，见 `delivery.json`。
