# T1 — 原文定位笔记（STATIC_ONLY）

只做定位与显式引用摘录，不判定论证是否成立。本文件不声称 cQ3/cQ4（或 IPL/SHE）推出原始 xi-f；未触碰 registry、fact-tree、既有证明、根目录配置。行号：III 各行为 `.txt`（`research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt`）行号；LANA 各行为 `.tex` 行号。

## 1 页序核验（printed_page 与 pdf_page_1_based 为何同值）

- `.txt` 内嵌 199 个 `===== PDF PAGE n =====` 标记（line 2 … line 11821）。
- PDF 自身：根页树仅 1 个 `/Type /Pages` 节点，其 `/Count` = 199；原始字节中 `/Type /Page` 页对象亦 199 个 ⇒ 标记数与页对象数一致。
- 抽取到的页眉页码若可判读（99 页），页码恒等于标记号，0 处不符（`tooling.log` §3）。
- 结论：本文件中 printed_page == pdf_page_1_based（无前置页偏移），两列同值写出。**未**逐页解码内容流做字节级比对，这是剩余方法缺口（§7-1）。

## 2 III Remark 3.9.5 — 何时保留什么、哪一步声称忘却什么

- **(viii) 8461–8472（p139）**：顺序为 sQ3（取 hull 的正张量幂行列式并施加 ⊼-形式）→ sQ4（用 log-Kummer 对应调整垂直位移）→ sQ5（经 realized semi-simplification 进入 log-volume）。**原文陈述。**
- **(viii) 8502–8512（p140）**：五条 (sub)quotient 操作之目的即"通过引入不确定量来简化"；其非平凡性在于"最小化商所引入的不确定量"与"保持与商之前既有结构的相容"之间的平衡；并称该计算 "essentially tautologically" 就是 Cor 3.12 的不等式。**原文陈述**（作者自述，非本任务的判定）。
- **cQ3 8546–8629（p141–142）**：hulls 被 O_K 乘法稳定 ⇒ 取行列式/正张量幂后落在 Θ×μ-LGP-link 陪域的局部与全局 Frobenioid 中，得到带 G_v 与 `O^×μ_{F_v}` 忠实作用的**对象**；⊼-形式以"⊼-category"取代集合论不变量。**保留**：G_v 与单位作用（即 F⊢×μ-prime-strip 部分）。**原文陈述。**
- **cQ4 8630–8642（p142）**：垂直位移的调整正是施加 log-Kummer 对应 ⇒ 该调整与此类同构"tautologically compatible"（或允许 log-link 任意迭代的不确定量，(Ob8)）。**原文陈述。**
- **iQ5 8643–8652（p142–143）**：进入 log-volume **恰恰等于忘却** local Galois groups 与 Frobenius-like units，即 F⊢×μ-prime-strip 部分（"amounts precisely to forgetting …"）。后续段落 8653 起跨页续写。**原文陈述。**
- **8659–8668（p143）**：cQ3/cQ4 = 该垂直列的"算术全纯性"/与 log-Kummer 对应相容；iQ5 = 忘却该算术全纯结构。**原文陈述。**
- **8672–8691（p143）与 8715–8719（p144）**：顺序不可交换 —— 闭合链必须**在应用 (sQ5) 之前**经过 (sQ3)、(sQ4)；略过 (sQ3) 或 (sQ4) 则链不闭合，"无法得出任何非平凡结论"。**原文陈述。**
- **8705–8711（p143–144）**：若省略 F⊢×μ 部分的子部分，则得不到同时带 Θ-intertwining 与 q-intertwining 的 strip。**原文陈述。**
- **我的解读（非原文）**：忘却动作集中在 (sQ5)→log-volume 这一步（iQ5）；cQ3/cQ4 是"忘却之前链条仍闭合"的全部依据。本任务不评价该依据是否充分。

## 3 III Remark 3.11.1 — IPL / SHE / APT

- 位置：(iii) 起于 9837；IPL 9844–9883（p160–161）；SHE 9884–9901（p161）；APT 在 (iv) 内 9925–9940（p162）。
- **IPL（原文）**：输出数据经算法内部操作诱导的 F⊩▶×μ-prime-strip 全多同构与**输入数据 prime-strip** 相连；每个"中间" strip 可同时充当 Theorem 3.11 算法的输入与 q-pilot 的 Kummer 理论输入；显式复合 = Remark 3.10.2 图中前两条下水平箭头的逆 + 第一条垂直箭头（Kummer 部分）+ 三条上水平箭头（evaluation 部分）。
- **SHE（原文）**：构造与输出数据"同时"相对于 Θ-link 域与陪域的算术全纯结构有效；并明确 SHE "对应于 Remark 3.9.5(viii),(ix) 的 (sub)quotient 链构成闭合环"（9898–9901）——SHE 与 §2 的唯一原文连接点。
- **APT（原文）**：不是集合论区域经集合论函数的搬运，而是"同时有效"的构造算法；方括号补充（9933–9940）指出算法输出的 "possible regions" 未必能与陪域结构直接比较，比较需要进一步技术（cf. 3.9.5(vii)）。
- **我的解读**：xi-b（10954–10955、10969–10972）把 IPL/SHE 当作前提性质使用；APT 是对 SHE 机制的刻画，不是独立前提。statement_role 中 IPL/SHE 记 asserted_compatibility、APT 记 definition，即按此区分。

## 4 Cor 3.12 证明 xi-d…xi-g（p183–185）

- **关键忘却声明在 (xi-b) 10965–10981（p182，未列入 CSV 单元，但为 xi-d 的直接上下文）**：Step (xi) 只关心 "qualitative logical aspects/consequences"，即 "temporarily forgetting" —— cf. HIS in Remark 3.11.1(iv) —— 该算法实际涉及 Θ-pilot objects、theta functions/values、mono-theta environments。**原文陈述。**
- **xi-d 11007–11047（p183）**：由 (xi-c) 得结论，输出数据改以 arithmetic vector bundle 局部化表述；随即指出必须取行列式并施加归一化 log-volume 才得到"完全可比对象"，且必须施加 1-column 的 log-Kummer 对应以校正垂直位移。**原文陈述。**
- **xi-e 11048–11072（p183–184）**：(SHE) 重述为"在输入 prime-strip 的 pilot-object log-volume 固定为 −|log(q)| 的条件下仍有效"；再得 R≤−|log(Θ)| 的结论。**原文陈述。**
- **xi-f 11073–11083（p184）**：目标包含关系与不等式 "then follows formally"。**原文陈述。**
- **xi-g 11084–11088（p184）**：总结；Fig. 3.8 本身在 p185。
- **我的解读**：xi-d→xi-f 中唯一的"忘却"动作是取 log-volume（对应 iQ5），"闭合"由 cQ3/cQ4 与 IPL/SHE 承载。CSV 的 statement_role 仅标记语句类型，不表示已核验。

## 5 LANA 三节（`.tex` 行号，无印刷页）

- **main goal 2502–2523**：目标写成待证等式 `eqn:SSEtaGoal`：存在合适的 S 使 `η^q = η^anab_S`。
- **eta-minimal 2525–2539**：输入 = BPS；链 étale-unit → log-shells → volume containers → R^ss；η 连接两条实线；`eqn:SSEtaGoal` 表示 η^q 落在 η^anab_S 的不确定量所生成的轨道中（Teichmüller 变形类比）。
- **provisional 2668–2680**：承认 SS 六边形不交换，但称自身分析不产生该图；关键在 `eqn:SSEtaGoal` "not manifestly false"；明确 **"we do not have a proof of (eqn:SSEtaGoal) at this time"（2677）**；不就可修复性表态；对是否存在可形式化证明无共识（2680）。
- **我的解读**：LANA 把争议定位到一条未证等式，与 III 中 cQ3/cQ4 ↔ xi-f 的缺口位置一致，但未给出该等式的证明。

## 6 与二级索引 `IUT_STAGE1_SOURCE_MAP.csv` 比对

- 页码逐条一致：P10 139–141、P11 141–144、P13 152;160–161、P16 160–166、P17 162、P20 183、P21 183–184、T01 184、E01 184–185。**无页码冲突。**
- 差异仅在颗粒度：(i) 索引 P16 把 SHE 并入 (iii)–(viii) 的 160–166，按单元定位 SHE 本体在 p161；(ii) 索引 E01 的 184–185 含 Fig. 3.8（p185），xi-g 正文止于 p184；(iii) 索引 P09 覆盖 (vii) 131–139，本任务未定位 (vii)。
- 索引 ROLE 与本表口径不同：索引把 xi-d 记 `DEFINITION_INSPECTED`（因该步显示 ℝ≤−|log(Θ)| 的定义），本表按"该步在论证中的角色"记 `inference`。属口径差异，非矛盾。

## 7 open

1. 页序仅以页树 `/Count`、页对象数、页眉页码自洽性核验；未逐页解码内容流比对（更强证据需 poppler `pdftotext -layout` 逐页切分）。
2. 3.9.5(vii) 的 (Ob1)–(Ob9) 原文未逐条定位（超出本任务范围），仅在他人单元的 explicit_references 中出现。
3. iQ5 段落 8653 起跨页续写；CSV 只覆盖标题段 8643–8652，续写段的显式引用未逐条摘录。
4. `statement_role` 词表无"否定相容"项：iQ5 记 `asserted_compatibility` 仅因它是对**相容性**的断言（极性见 anchor 的 "Incompatibility"），**不得**读作与 cQ3/cQ4 同类。
5. LANA 只有 `.tex`，未与任何排版版核对。
6. 索引 CSV 的 III 行 SHA256 与本地 PDF 相同（同一文件），但 `SOURCE_FILE` 写作 `sources/IUT_III.pdf`、本地缓存文件名不同 —— 仅记录，未改动。
