# N02 核心争议与回应矩阵（摘要）

日期：2026-10-23。目录 `handoffs/non-lean-2026-10-23/N02/`。状态：`PARTIAL`。本表是来源索引，不是数学结论，不裁决谁对。

- **12 个争议项**（`controversies.csv`），覆盖 (a) 3.11→3.12 推演 C01–C03、(b) 跨结构识别 C04–C06、C12、
  (c) 归一化 C07–C08、(d) 合法输出/存在性 C09–C10、(e) log-volume C11–C12（有交叉）。
- 每项**双方一级来源都落到本地行号 + 页码**：
  - 作者方 `iut3` = `research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt`（带 PDF 页标记）；
    `rpt2018` = 望月 2019 年 3 月讨论报告（本地 txt，无页标记，只给行号）。
  - 批评方 `ss-local` = **本地第三方转录**（DrAbx123 仓库 vendored 的 Scholze–Stix 文本）；官方 PDF 在本环境
    无法取回（`web_fetch` 返回 unsupported content type application/pdf）→ **官方身份 UNRESOLVED**，
    页码依转录内页眉推定，`loc` 里已注明。
  - 第三方 `lana` = `LANA-interim-report-2026-07.txt`（带页标记），既是独立分析也是 (9-1) 目标来源。
- 最要紧三对锚点：
  1. `iut3` l.11080–11083（p.184）"then follows formally" ↔ `ss-local` l.661–662（p.10）"leads to an empty inequality"。
  2. `iut3` l.10512–10520（p.174）Θ 侧受 Ind1/2/3、q 侧"we do not regard as subject" ↔ `ss-local` l.616–619（p.9）把它读成
     "identification of concrete Theta-pilot objects and concrete q-pilot objects"。
  3. `rpt2018` l.1132–1150 (AD)/(IUAD)：作者明言 j² 不相容在**单一环结构内**成立且"absolutely no dispute"，
     分歧点是两侧是否为**不同**的算术全纯结构 —— 本表里唯一由作者主动划界的句子。
- 归一化的硬事实：III 只允许**无权重平均**（`iut3` l.7247–7271，p.119–120 明答"no"），
  而 S–S 建议用 average 绕过 j²（`ss-local` l.574–576、l.657–659）。双方对"average 能否吸收 j²"没有共同前提。
- LANA 侧：承认 Figure 7 不交换（l.2274–2276），但主张 3.12 不是比较 Θ-link 两侧的两个 pilot（l.2221–2226、2240–2243），
  并自认未证 (9-1)（l.2281–2282）。
- **边界**：不声称穷尽异议（Joshi、Dupuy–Hilado、Urahigashi Step(v) 等不在 12 项内，见 `research/controversies.md` C04–C06），
  **不声称学界共识**；LANA 自己记录成员未达成一致（l.2291–2293）。
- 与 v1 的关系：本目录原有一份 9 行 v1（`make_N02.py` 生成，末列名 `tag`、S–S 侧只有 URL、无任何 IUT III 锚点）。
  本版扩到 12 行并补齐 IUT III / RPT2018 / ss-local 行级锚点；v1 生成器已改名 `make_N02_v1.py.retired`
  （防止重跑静默回退），v1 的 sha256 记在 `delivery.json`。K→C 映射见 `notes.md`。
- 复算：`py -3 verify_N02.py` 对 38 条锚点做机械核对（行号+页码），当前 0 FAIL。
- 所有 12 项的"判定所需证据"仍缺（见 `what_would_settle_it` 列）；关联 GAP 全部保持 OPEN。
