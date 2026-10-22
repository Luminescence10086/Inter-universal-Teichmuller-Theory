# T1 摘要（STATIC_ONLY；未经编辑器检查；未准入 fact-tree）

- 交付：`source-map.csv`（15 行，列完整）、`notes.md`、`tooling.log`、本文件、`delivery.json`。仅写入 `handoffs/core-support-2026-10-22/T1/`，未改动 registry / fact-tree / 既有证明 / 根配置。
- 单元：III 12 行（R3.9.5 的 cQ3/cQ4/iQ5/(viii) sQ3-sQ4-sQ5 顺序/(ix) 闭合环；R3.11.1 的 IPL/SHE/APT；Cor3.12 的 xi-d/e/f/g）+ LANA 3 行（main goal / eta-minimal / provisional assessment）。全部 `UNRESOLVED` = 0。
- 输入哈希（实测，`tooling.log` §1）：PDF `9a7ee3c7…91a0b9`（与交接单一致）；TXT `70a618ad…64b715`（交接单未钉，本任务作为输入哈希记录）；LANA.tex `a12653a8…8248585`；索引 CSV `4a5b964f…219731`。
- **LANA commit 缺陷**：交接单 `293bddf89463473ae13d40834d70fb4b7ba81da1f` 为 41 位十六进制（非法 SHA-1）；实测 `git -C reviews/core-round/external/LANA_report_202607 rev-parse HEAD` = `293bdd89463473ae13d40834d70fb4b7ba81da1f`（40 位，仅少交接单插入的那个 `f`）。按交接单口径记为**交接单笔误**，status 保持 `STATIC_ONLY`，不记 `INPUT_DRIFT`；两串原文见 `delivery.json` 的 `inputs[2]`。
- 页序：`.txt` 199 个页标记 = PDF 页树 `/Count` 199 = `/Type /Page` 页对象 199；可判读页眉页码的 99 页中页码 == 标记号，0 处不符 ⇒ 本文件 printed_page == pdf_page_1_based，两列同值。未逐页解码内容流（见 `notes.md` §7-1）。
- 与二级索引：页码无冲突；仅颗粒度差异（SHE 在 p161 vs 索引整块 160–166；xi-g 正文止于 p184，索引 184–185 含 Fig.3.8）；索引把 xi-d 记 `DEFINITION_INSPECTED`，本表按论证角色记 `inference`，属口径差异。
- 未升级：本交付不含任何"cQ3/cQ4 ⇒ xi-f"或"兼容性已证"的断言；`notes.md` 严格区分原文陈述与我的解读。
- open：① 未做内容流级页序比对；② (vii)(Ob1)–(Ob9) 未定位；③ iQ5 跨页续写段（8653 起）引用未摘；④ 词表无"否定相容"项，iQ5 的极性见 anchor；⑤ LANA 无排版版可核。
- `started_at` 取本任务第一个落盘工件的时间戳（此前为只读检视，约早 8 分钟，无可靠时间戳可引）。
