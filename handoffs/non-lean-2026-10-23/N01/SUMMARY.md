# N01 — 官方报告与缓存版本核对

状态：`STATIC_COMPLETE`（来源版本证据；不是数学审阅）

## 结论三句话
1. 本轮从官方 GitHub（`katobungen/LANA_report_202607`，`pdf` 分支）取到了 `LANA_report_202607.pdf`：
   640,461 B，`sha256 aa53093aa8d69dbce5f8fb4f541069a418650260dee1ef532917aa8db89606c7`，50 页，正文日期 **July 20, 2026**。
2. 工程里一直在用的缓存 `research/round2-source-cache/LANA-interim-report-2026-07.pdf`：
   640,457 B，`sha256 a368345c1b4f03d9dba439cee7d3b186465b802233392b1fc7727edec8be2f30`，50 页，
   日期 **July 16, 2026**；它与 ncatlab 镜像**字节完全相同**。
3. 因此"同一标题"成立，"相同字节"不成立，差异可定位到 2 处（日期行、致谢段人名与断行）。见 `diffs.md`。

## 已核实 / 未核实
- 已核实（`SOURCE_FACT`）：字节哈希、页数、日期行、致谢段两处文本差异、镜像与缓存的字节同一性。
- 未核实（`UNRESOLVED`）：zen.ac.jp 页面本身只是链接页，本轮抓到了 HTML 但没有从中再取到第三个独立副本；
  7 月 20 日版与 7 月 16 日版之间是否存在**数学内容**改动，只核对了文本层 2 处差异，未逐节重读全文。

## 影响
- 工程内此前引用 LANA 报告页码/措辞（例如 `research/core-backward-2026-10-23/lana-report-assessment.md`）
  依据的是 **7 月 16 日版**；若某条引文的页码落在致谢或日期附近需重对，其余正文未见文本差异。
- 旧缓存保留未动。
