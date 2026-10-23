# N15 补丁建议：需要改动的原文档

只提建议，**不实施**。N15 未改任何主线源码、配置、旧收据、GAP 文件或 `fact-tree/registry.json`。
每条给出：文件 · 行号 · 建议改法 · 理由（理由只引用可在本仓库复算的证据）。

优先级：**P1 = 会误导下一位执行者或读者**；P2 = 会误导渲染/计数；P3 = 卫生问题。

---

## P1-1 · `research/core-backward-2026-10-23/PATH.md` 第 49–51 行

- 现状：`**下一步（未开始，且不再是玩具层）**：…在拿到那些对象之前，本路径到此为止，核心 GAP 保持 OPEN。`
- 建议：**删去 49–51 行**；若要留痕，改为一行 `（历史：2026-10-23 早期版本的"下一步"，已被第 75 行小节取代——W10/W11/W12 已在之后交付。）`
- 理由：同一文件里有两个"下一步"（49–51 与 75–82），前者说路径已停，后者给出 1–4 步并已排定；
  且 32–35 行已收录 W10–W12 三项后续产物，正说明 49 行"到此为止"已不成立。读者按 49 行会以为动线结束。

## P1-2 · `research/core-backward-2026-10-23/round-report.md` 第 152–157 行

- 现状：`## 下一步（不属本批次的机械任务）` 列 4 条。
- 建议：标题改为 `## 下一步（2026-10-23 已过时，现行动线见 PATH.md 第 75 行起）`，并在四条前加一句
  `其中 #2 已由 K4、#3 已由 W8/W9/W10、#4 已由 W12 覆盖；#1 见 h1-decision.md。`
- 理由：4 条里 3 条已被后续交付覆盖（PATH.md 第 20、32、35 行分别记 K4、H3Synthesis、LabelNormalization）；
  三份文档（PATH 两处 + round-report 一处）各说一套"下一步"，是当前最容易被误读的重复。

## P1-3 · `handoffs/non-lean-task-catalog-2026-10-23.md` 第 13 行

- 现状：`开始整理时的本地 HEAD：1a8515d88084e5283d02ea918131c7faed38a7da。这只是快照标识。`
- 建议：改为 `开始整理时的本地 HEAD：1a8515d8…（已被 568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2 取代；两者都只是快照标识，不作输入 pin，输入一律按文件 sha256 固定）。`
- 理由：`git rev-parse HEAD` 现为 `568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2`；`N04/SUMMARY.md` 第 24 行已把同一漂移记为 `INPUT_DRIFT`。
  按旧串复算的人会对不上，而这不是真漂移。

## P1-4 · `handoffs/non-lean-task-catalog-2026-10-23.md` 第 84 行

- 现状：N04 输入写 `Iut/Concrete/LocalConstruct/Arithmetic.lean`、`LogShell.lean` 及**最多两个**直接依赖。
- 建议：改为 `Integral.lean`、`MaximalOrder.lean`、`ResidueField.lean`（`LogShell.lean` 保留为对照），
  并把依赖预算改为**至多四个**；同时保留一句"`Arithmetic.lean` 已核：不含 tensor order / maximal order / 分解 / 有限商"。
- 理由：`N04/SUMMARY.md` 第 7 行已核该文件 223 行不含所需任何一项，材料全在导入链下游三文件；
  N04 实际用了 4 个依赖（Arithmetic/LogShell/Integral/MaximalOrder/ResidueField/Packet），预算与事实不符。

## P1-5 · `handoffs/non-lean-task-catalog-2026-10-23.md` 第 171 行

- 现状：`余下十项的重新标记仍被其交付记录明确留给复核者。`
- 建议：句末加 `（2026-10-23 已由 N14 逐项裁定：21 项中 SUPPORTED 6 / INSUFFICIENT 6 / STALE 2 / MISSING 7，见 handoffs/non-lean-2026-10-23/N14/receipt-review.csv。）`
- 理由：该句描述的是"尚未裁定"，而 N14 已给出全部 21 行判词；照旧句读会以为十项仍悬空。

## P1-6 · `handoffs/next-round/README.md` 第 3 行、第 18–27 行

- 现状：2026-10-21、基线 `4841271…` 的**上一轮**交接，自带另一套交付契约（`bundle.json`，见同目录 `bundle.example.json`）。
- 建议：首行加 `（历史轮次：其交付契约已被 handoffs/non-lean-task-catalog-2026-10-23.md 第 3 节的 delivery.json 契约取代。）`，
  或整体移入 `handoffs/archive/`。
- 理由：同一 `handoffs/` 下并存两套"交付包"契约且同名不同物（`bundle.json` vs `delivery.json`），
  新 agent 会挑错模板；本轮已交付的 N 任务一律按 catalog §3 写。

---

## P2-7 · `research/core-backward-2026-10-23/PATH.md` 第 31、34、36 行

- 现状：三处空行把"已经走过的"一张表切成 3 张（W10/W11 一张、W12 一张）。
- 建议：删去 31、34、36 三个空行（或把 32–35 四行并入 17–30 的主表），保持一张表。
- 理由：markdown 表被空行截断后，渲染成三段、表头断掉；按行号引用表行的人会取错段。

## P2-8 · `research/core-backward-2026-10-23/PATH.md` 第 96–97 行

- 现状：`每一步都跑三关（… / 编辑器 0 error、0 warning），并把"未做/未读/属推断"的地方写清。`
- 建议：改为 `… 第三关为**目标**；W 系列中只有 6 项有本文件级编辑器收据（其余 INSUFFICIENT / STALE / 无收据），裁定见 N14/receipt-review.csv。`
- 理由：N14 的 21 行判词是 SUPPORTED 6 / INSUFFICIENT 6 / STALE 2 / MISSING 7；
  把"窗口无诊断行"读成"该文件验过"正是 N14 明确否掉的那种读法。

## P2-9 · `research/core-backward-2026-10-23/PATH.md` 第 35 行（W12 行）

- 现状：`M-iii 落地：… 证二者在"标签集就是轨道"时相等 …`
- 建议：把 `M-iii 落地` 改为 `M-iii 在 hAct（标签集=轨道）假设下对齐`，并在句末加 `（假设失效时的反例见同文件；见 N13 风险卡）`。
- 理由：`N13/SUMMARY.md` 第 23 行已认定 `averageOverLabels_eq_averageOverOrbit` 只在 `hAct` 下成立，
  且文件自设反例（`ZMod 3` 上 2 vs 1）恰使 `hAct` 为假——"落地"是集成层过述。

## P2-10 · `research/core-backward-2026-10-23/PATH.md` 第 84、86 行

- 现状：`## 玩具层的边界（重要）` / `到 W10 为止，所有 Lean 产物都在玩具层…`
- 建议：`到 W10 为止` → `到 W12 为止`，并在括号里补 `（W11、W12 同属玩具层）`。
- 理由：第 33、35 行已收录 W11、W12，二者同样是 `localLog` / `ℚ_[3]` 玩具层产物；范围陈述与产物表自相矛盾。

## P2-11 · `handoffs/core-residue-certificates-2026-10-23.md` 全文件

- 现状：3 440 B 的旧交接，工作区每份 `delivery.json` 的 `inputs[]` 中**被引用 0 次**（机械核对，逐份可复算）。
- 建议：首行加 `（未被 2026-10-23 本轮任何任务采用；其对象对应尚未交付的 N08/N09。）`
- 理由：无引用的交接文件与"已消费输入"外观相同，容易被当作已实现依据；同批无引用的还有
  `handoffs/core-support-2026-10-22.md`（T1–T4 的 brief，0 次被引用），建议同样标注。

---

## P3-12 · `candidates/core-transport/TransitionCompatibility.lean` 第 634–637 行

- 现状：4 行 `#print axioms`（`PresentationChain.stepInv_step` / `.relativeInput_mem` / `.reading_hasSum` /
  `.reading_is_limit_of_algorithm`）与第 596、593、594、595 行**重复**。
- 建议：删去 634–637；若要保留，则另写一段说明为何二次导出，并重跑一次 CLI/公理关以刷新收据。
- 理由：`N13/SUMMARY.md` 第 26 行已把该重复记入风险卡；重复行会让"declarations : axiom reports"这类
  1:1 计数虚高，收据的机械核对会失真。**本项属主线源码，必须由主线改并重跑三关，N15 不动它。**

---

## 附：未提出建议的地方（避免越界）

- 三份 `GAP-core-*.md` 的 OPEN 状态与本轮交付不冲突，**不建议改动**；只有"关闭 GAP"才需要新证据。
- `fact-tree/registry.json`（332 365 B）**不在任何建议范围内**：准入需要真实编辑器验证与主线流程。
- N14 的 `receipt-review.csv`、各 `W*/editor/*`、`lean_stdout/stderr` 等**旧收据一律不提议改写**；
  P3-12 已注明需"重跑刷新"而非就地编辑。
