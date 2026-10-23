# N02 备注：直引 / 解释 / 未找到来源

本文件是 `controversies.csv` 的证据分级说明。引文一律可在本地文件按行号复算；`py -3 verify_N02.py` 对
38 条锚点做机械核对（snippet 命中行 + PDF 页号双重比对），2026-10-23 运行结果 **38/38 PASS，0 FAIL**。

## 0. 引用约定（先读，否则按字面 grep 会失配）
本地 IUT III / LANA 文本是 PDF 抽取结果，希腊字母与上标部分丢失或乱码（Θ、ℓ、²、⊞ 等）。因此 CSV 中的
引文做了**统一音译**：`Θ → Theta`、`ℓ → l`、`j² → j^2`、`⊞ → box`、`≤/≥ → <=/>=`、`ﬁ → fi`。
除这些替换外，引文与原文逐字一致；`verify_N02.py` 的 snippet 全部选用不受音译影响的 ASCII 片段。
**不得**把 CSV 里的字符串当成可直接粘贴的原文引文使用。

## 1. 直引（本地可复算，`SOURCE_FACT_ANCHORED`，10/12 行）
- `iut3`（IUT III 官方 2020 预印本文本，sha256 `70a618ad…4b715`，199 个 `===== PDF PAGE n =====` 标记）：
  Cor 3.12 陈述 l.10498–10528（p.173–174）、证明 (xi-d)–(xi-f) l.11016–11083（p.183–184）、(xi-g) l.11084–11088、
  Remark 3.11.1(i)(ii) l.9780–9821（p.159–160）、Ind1–3 l.668–684（p.12）、Thm 3.11(i)(a) l.9344–9345（p.153）、
  Prop 3.9(i) l.6974–7017（p.115–116）、Remark 3.9.3 l.7247–7271（p.119–120）、Remark 3.9.5(i)+(Ob5) l.7786–7808、
  l.8190–8208（p.127、p.134）、introduction p.1 l.31–37。
- `rpt2018`（望月《Report on discussions, March 15–20, 2018》，本地 txt，sha256 `5ab53862…9c69eb`，**无页标记**）：
  (AD) l.1132–1140、(IUAD) l.1142–1150、(ADItw) l.1154–1160、(MlLV) l.1205–1214、(LbEx5)/(LbEx6) l.1559–1590。
  该文件是作者本人对这轮讨论的书面回应，是本表**唯一**能定位到"作者究竟反驳哪一句"的一手材料。
- `lana`（LANA 中期报告文本，sha256 `5fc6185d…e040e`，`===== PAGE n =====` 标记）：§9.2 l.2126–2141（p.45–46）、
  §10.2–10.4 l.2172–2273（p.47–49）、§10.5 l.2274–2293（p.49）、Step 9 的 upper semi-compatible l.2114–2116（p.45）。

## 2. 解释（`INTERPRETATION_BRIDGE`，2/12 行）
- **C08**（两边的归一化是否同一）：S–S 与 III 的句子都是直引，但"两边是否处在同一归一化"是我方组织的判定问题，
  原文没有一句话直接讨论"packet vs procession 是否一致地用在 3.12 两侧"。
- **C09**（"可能像之并的 hull" vs "对象认同"）：S–S 的句子直引，"S–S 把 3.12 读成对象认同"这一归因是我的读法，
  不是他们的原话；C09 的判定因此只能算**待核**。
其余 10 行的 `claim_A/claim_B` 都是逐句引文（经第 0 节的音译）。

## 3. 没找到来源 / `UNRESOLVED`
- **1 项系统性缺口**：Scholze–Stix 官方 PDF 本地**没有**。本表用的是本地第三方转录
  `reviews/core-round/external/DrAbx123--Formalization-of-Inter-universal-Teichmuller-Theory-IUT-and-abc-conjecture/vendor/promachina/snapshots/0d52e0fd5b53/docs/scholze-stix-why-abc-is-still-a-conjecture.md`
  （sha256 `6c0f7281…4b354f`，687 行）。内容与 LANA 转述、与 `research/controversies.md` 的页码定位一致，
  但**字节同一性未核实**；本环境的 `web_fetch` 对该 URL 返回 `unsupported content type "application/pdf"`
  （只尝试 1 次，未重试）。→ 引用 S–S 具体句子前必须取得官方 PDF 逐字核对。
- **页码**：`ss-local` 无 `===== PAGE n =====` 标记，只有页眉（l.50 p.2、l.113 p.3、l.174 p.4、l.247 p.5、l.305 p.6、
  l.400 p.7、l.491 p.8、l.577 p.9、l.633 p.10）。CSV 的页码由这些页眉**推定**，`loc` 中已标 `page inferred`/`p.8` 等；
  其中 p.10 与 LANA 独立引用的 `[15, pp.9-10]`、`[15, p.10]` 一致（这是唯一的外部交叉校验）。
- **0 项**完全没有双方来源：12 行都同时有 A/B 两侧的本地行号锚点。
- 遗留：v1 的 K08（IUT IV Step (v) 局部非包含）原文仍未定位（本地 IUT IV 文本无对应行），本表不再列该项，
  其状态保持 `UNRESOLVED`，见 `research/controversies.md` §5。

## 4. v1 → v2 差异（查缺项记录，不重写历史）
本目录原有一份由 `make_N02.py` 生成的 9 行 v1。可核对的 v1 字节：
`controversies.csv` sha256 `36c58b9b…ab9fc5`（本机在 20:04:49 回退后实测两次，与 v1 自报一致）、`delivery.json` sha256 `31720d02…eb22`（实测，见下）、生成器 `make_N02.py`（现名
`make_N02_v1.py.retired`，sha256 `502a1f85…1964`，实测，且与 v1 delivery 自报一致）。
v1 的 `SUMMARY.md` / `notes.md` 原 sha256 只由 v1 `delivery.json` **自报**（`8e84c915…`、`51dba87d…`），
两文件此后已被 v2 覆盖，本站无法再复算 → 该两值记为 `UNRESOLVED`（不可复算），不作为证据使用。
v1 的缺口：① 末列名是 `tag` 而非契约要求的 `status`；② S–S 侧只有 URL、无本地行号；③ **完全没有 IUT III 锚点**
（作者方只引 LANA）；④ 未用本地的望月 2018 回应；⑤ (c)(e) 两轴未拆开，且把 (e) 误标为"IUT IV 局部非包含"。

| v1 | v2 | 处理 |
|---|---|---|
| K01 scale/hexagon | C01 + C06 | 拆成"形式跳跃"与"是否经六边形"两项 |
| K02 Theta-link / alien ring | C04 | 保留，补 IUT III p.1 / Remark 3.11.1(ii) 与 S–S 2.1.9 行号 |
| K03 (9-1) 本身 | C12 | 保留，补 III (xi-g) 作为对照面 |
| K04 hull 与不定性大小 | C09 + C11 | 拆成"集合语义"与"非空性" |
| K05 Cor 3.12 是争点 | C01 + C10 | 落成"形式跳跃"与"Θ/q 不对称"两项 |
| K06 Dupuy–Hilado / K07 Joshi | （移出 12 项） | 不属 (a)–(e)；保留在 `research/controversies.md` C04–C05 |
| K08 Urahigashi Step (v) | （移出 12 项） | 属 IUT IV，非本任务五轴；仍 `UNRESOLVED` |
| K09 "什么算解决" | 并入每行 `what_would_settle_it` + C11 | 结构化到列 |
| —（新增） | C02, C03, C05, C07, C08 | abstract/concrete pilot、3.11 的地位、labels、j 平均、归一化 |

v1 生成器 `make_N02.py` 已改名 `make_N02_v1.py.retired`：原因是本目录在 2026-10-23 20:04:49 出现过一次
"重跑生成器把已写入的 v2 CSV 整体回退为 v1"（CSV sha256 回到 `36c58b9b…`），与项目中"生成型脚本 + 哨兵 = 直改被静默回退"
的既有实案同型。保留其源码（可读、可复现 v1），但改名使后续任何 watch/重跑不会覆盖 v2；`delivery.json` 记录 v1
**可核对**的 sha256（CSV、delivery.json、生成器三项），v1 的 `SUMMARY.md`/`notes.md` 哈希不可复算，已按 `UNRESOLVED` 记。

## 5. 三条纪律
1. 不声称穷尽所有异议，也不声称存在学界共识（LANA l.2291–2293 自己记录成员未达成一致）。
2. 模型反例（S–S 六边形、各类 toy）不自动构成对原理论的否定；`minimal_disputed_statement` 列的作用就是把异议
   精确到"反驳的是哪一句"。
3. 二手/转录来源的引文不能当作一级来源使用；本表所有 S–S 行都带 `ss-local` 标记，即此意。

## 6. 复算命令
```
cd handoffs/non-lean-2026-10-23/N02
py -3 verify_N02.py                       # 38 条锚点：行号 + PDF 页号
py -3 extract_anchors.py hash             # 四个输入文件的 sha256
py -3 extract_anchors.py show iut3 11073 11083   # 按行号+页码打印原文
py -3 extract_anchors.py grep ss 'monodromy j'
```
两个脚本均只读，不联网、不调用 Lean/Lake。
