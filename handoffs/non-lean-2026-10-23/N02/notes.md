# N02 备注：哪些是直引、哪些是二手、哪些没找到

## 直引（本地可复算，`SOURCE_FACT`）
- `LANA-interim-report-2026-07.txt`：9.2 行 2138-2141（p.45-46，"(9-1)" 的存在型表述）；10.5 行 2274-2293（p.49-50，
  "the diagram in Figure 7 does not commute"、"we, the LANA project, do not have a proof of (9-1)"、"unable to reach
  complete consensus"）。行号与页码都按本地检索文本，可复算。
- `research/controversies.md` 的条目结构（C01–C05）本轮**复用**，未重写整部发展史。

## 二手（`SECONDARY_DIGEST`）
- Scholze–Stix 的两篇（`WhyABCisStillaConjecture.pdf`、`Cmt2018-08.pdf`）、Joshi 的报告、Dupuy–Hilado 的两篇：
  本地**没有**原文副本，本表的内容来自 `research/controversies.md` 的摘录与页码定位（该文件 2026-10-16 记录）。
  凡是这一类的行，`tag` 列都标 `SECONDARY_DIGEST`，表示"引文来自二手摘录，未与原文逐字对校"。

## 没找到来源（`UNRESOLVED`）
- K08 的 IUT IV Step (v) 原文：本地源缓存里没有 IUT IV 的对应行，因此**没有**给出反引文，只说"该异议未被本项目复现"。
- K02 的"Θ-link 是否必须是环同态"：两种读法在文本上都站得住，本表不裁决。

## 三条纪律
1. 不声称穷尽所有异议，也不声称已形成学界共识（LANA 自己都写明无共识）。
2. 模型反例（如 SS 的六边形）不自动构成对原理论的否定；要否定必须精确到"反驳的是哪一句"。本表 `minimal_disputed_statement`
   列就是这个用途。
3. 二手来源的引文不能当成一级来源使用；若要引用 SS 的具体句子，需先取得原文并逐字核对。
