"""N02 -- controversies.csv, notes.md, SUMMARY.md, delivery.json.

Sources used, and how each is graded:
  * LANA report text  -> locally quoted, line numbers + PDF page (SOURCE_FACT for the quote itself)
  * IUT III text      -> locally quoted, line numbers + page (SOURCE_FACT)
  * research/controversies.md (2026-10-16) -> the route to the Scholze-Stix / Mochizuki / Joshi / Dupuy-Hilado
    primary documents; their content is quoted from that digest and marked SECONDARY_DIGEST, with the
    URL recorded. Where no local copy of the primary text exists, the row says so instead of pretending.
"""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N02 = ROOT / 'handoffs/non-lean-2026-10-23/N02'
LANA = 'research/round2-source-cache/LANA-interim-report-2026-07.txt'
III = 'research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt'
DIGEST = 'research/controversies.md'
SS = 'https://www.math.uni-bonn.de/people/scholze/WhyABCisStillaConjecture.pdf'
SSREPLY = 'https://www.kurims.kyoto-u.ac.jp/~motizuki/Cmt2018-08.pdf'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


ROWS = [
    ('K01', 'scale / single-value compatibility (the hexagon)',
     'the diagram in their Figure 7 cannot be made to commute: a consistent identification forces a j^2, and a '
     'consistent scale removes the very j^2 the argument needs',
     'Scholze-Stix, Why abc is still a conjecture, sec 1.3 pp.3-4 and sec 2.1.8-2.2 pp.8-10', SS,
     'the identification is not performed inside one holomorphic structure; each prime-strip carries its own ring '
     'theory and the scale is not simultaneously forgotten and kept',
     'Mochizuki, Comments on the manuscript (2018-08), C10-C14 pp.3-4', SSREPLY,
     'can the abstract prime-strip generators be identified with concrete degrees by a map that is typed on both '
     'sides, without either losing or duplicating the j^2?',
     'a typed diagram whose every arrow is either an isomorphism, a natural transformation, an inclusion or an '
     'equality of reals, checked for consistency end to end',
     'GAP-core-comparison-reconstruction.md', 'SECONDARY_DIGEST (both texts reached via research/controversies.md; '
     'no local copy of either PDF)'),
    ('K02', 'Theta-link and the alien ring structure',
     'the two ring structures (before and after the link) cannot both be used while one of them is discarded; the '
     'link is a non-ring-theoretic identification',
     'Scholze-Stix, same document', SS,
     'the link is by definition an identification that is not compatible with the ring structures; calling it an '
     'isomorphism and then forgetting one side is the point of the construction',
     'LANA report, the eta-algorithm discussion (it restates the goal instead of adjudicating)',
     LANA,
     'is the Theta-link required to be a ring map, or is the whole construction a non-ring-theoretic transport by '
     'design? Either reading is defensible on the surface; only a formal definition settles it',
     'a formal definition of the link and a proof that the rest of the argument uses only what that definition gives',
     'GAP-core-native-realization.md', 'UNRESOLVED (the two readings are both textually supported)'),
    ('K03', 'the (9-1) compatibility itself',
     'the final numerical inequality needs (9-1); the LANA assessment of the SS diagram accepts that the diagram does '
     'not commute but then argues the proof need not factor through it',
     'LANA report 10.5, lines 2274-2293 (p.49-50)', LANA,
     'the diagram does not commute, but the eta-algorithm does not give rise to that diagram; the inequality hinges '
     'on (9-1), which is "not manifestly false"; and the project has no proof of (9-1)',
     'LANA report 9.2, lines 2138-2141 (p.45-46)',
     LANA,
     'is (9-1): exists a suitable S with eta_q = eta_anab_S, and does the argument factor through the commuting '
     'diagram at all?',
     'a proof of (9-1), or a proof that the inequality can be obtained without it',
     'GAP-core-comparison-reconstruction.md', 'SOURCE_FACT'),
    ('K04', 'log-volume of hulls and the size of the indeterminacy',
     'the indeterminacy must be absorbed by hulls; if absorbing it costs too much, the resulting bound is vacuous',
     'Scholze-Stix (the l^2-level loss objection), as summarised in research/controversies.md C01', SS,
     'the log-volume is taken on the hull of the possible images, so the indeterminacy is inside the object being '
     'measured rather than multiplying it afterwards',
     'LANA report, lines 2270-2273 (p.49)', LANA,
     'does the hull-of-images operation keep the log-volume small enough to yield a non-vacuous inequality?',
     'an explicit computation of the hull log-volume for one q-pilot, with the indeterminacy included',
     'GAP-core-residue-hull-realization.md', 'SOURCE_FACT for the LANA side; SECONDARY_DIGEST for the SS side'),
    ('K05', 'Corollary 3.12 as the disputed step',
     'the step from Theorem 3.11 to Corollary 3.12 is where copies of the real line are identified, and that is the '
     'problem',
     'LANA report 10.5, lines 2283-2289, which states this as the point the two reports share', LANA,
     'the identification of copies of R is indeed the issue, but it does not follow that the argument cannot be '
     'repaired',
     'LANA report 10.5, line 2289-2290', LANA,
     'is the identification of copies of R in the 3.11 -> 3.12 step legitimate, and is it the only place where it happens?',
     'a formal statement of that step with all copies of R indexed, plus a proof that the identification used is the '
     'one proved available',
     'GAP-core-comparison-reconstruction.md', 'SOURCE_FACT'),
    ('K06', 'conditional consequences are not a repair',
     'results built on Cor 3.12 (and Claim 5.0.1) are conditional; a footnote in the Szpiro paper suggests the actual '
     'Ind1 action includes a permutation across tensor factors that the toy omits',
     'Dupuy-Hilado, arXiv 2004.13228v1 and 2004.13108v2 Thm 1.0.3-1.0.5, sec 6.2 footnote 7 (via the digest)',
     'https://arxiv.org/abs/2004.13228',
     'those results are explicitly conditional on Cor 3.12, so they neither confirm nor remove the obligation',
     'LANA report 10.5 on the absence of a proof of (9-1)', LANA,
     'do the conditional results assume the very step in dispute, and does the omitted cross-factor permutation matter?',
     'a formalisation of the conditional statement with its hypotheses as theorem parameters, plus a verified model '
     'of the cross-factor permutation',
     'GAP-core-comparison-reconstruction.md', 'SECONDARY_DIGEST'),
    ('K07', 'alternative frameworks do not discharge the obligation',
     'the arithmetic holomorphic structures are not quantified precisely enough to justify existence and comparison '
     'of several such structures; an alternative framework supplies it',
     'Joshi, Final Report on the Mochizuki-Scholze-Stix Controversy, sec 1.2-1.4 (2025 v1)', 'https://arxiv.org/html/2505.10568v1',
     'an alternative framework is a different theory; it does not retroactively prove the original steps',
     'research/controversies.md C04 (this task does not audit Joshi either)', DIGEST,
     'does the alternative framework imply the original Cor 3.12 statement, or only an analogue inside the new framework?',
     'an explicit translation theorem from the alternative framework back to the original statements',
     'GAP-core-native-realization.md', 'SECONDARY_DIGEST'),
    ('K08', 'local non-containment objection (IUT IV step (v))',
     'a local containment relation used in IUT IV step (v) fails in an explicit short computation',
     'Urahigashi, stepv-local-noncontainment (tag v0.8.0)',
     'https://raw.githubusercontent.com/turahigashi/iut-explicit-initial-theta/v0.8.0/stepv-local-noncontainment/paper/stepv_local_noncontainment.tex',
     'this is a separate, local objection; nothing in the project has yet reproduced the computation',
     'IUT IV step (v): not located in the local source cache, so no counter-quote is given here', 'UNRESOLVED',
     'does the containment used in step (v) hold with the exact hypotheses of the paper (in particular non-archimedean '
     'places only, and the stated normality)?',
     'an independent recalculation at one place, either reproducing the failure or finding the hypothesis that excludes it',
     'GAP-core-residue-hull-realization.md', 'UNRESOLVED'),
    ('K09', 'what would count as settling the dispute',
     'the disagreement is not about definitions but about whether a certain identification is legitimate',
     'the two bodies of text quoted above', DIGEST,
     'the LANA report states that the members could not reach consensus on whether the original contains a formalisable proof',
     'LANA report 10.5, lines 2290-2293', LANA,
     'a formalised proof of (9-1), or a formalised refutation of the step 3.11 -> 3.12, would settle the specific '
     'question; opinions about the possibility of repair would not',
     'a machine-checked statement of either side, with the disputed step as an explicit hypothesis',
     'GAP-core-comparison-reconstruction.md', 'SOURCE_FACT'),
]

rows = ['id,topic,claim_A,source_A,loc_A,claim_B,source_B,loc_B,minimal_disputed_statement,what_would_settle_it,related_gap,tag']
for r in ROWS:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in r))
(N02 / 'controversies.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

notes = """# N02 备注：哪些是直引、哪些是二手、哪些没找到

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
"""
(N02 / 'notes.md').write_text(notes, encoding='utf-8')

summary = """# N02 — 核心争议与回应矩阵

状态：`STATIC_COMPLETE`（分歧与出处索引；**不裁决**谁对）

## 范围与做法
9 个争议项，覆盖 (a) 3.11→3.12 的推演、(b) 跨结构识别/Θ-link、(c) 归一化与 log-volume、(d) 合法输出/存在性、
(e) 局部非包含异议、(f) 条件式后果与替代框架。**复用** `research/controversies.md`（C01–C05），不重写发展史。
每项记录：双方主张、出处（本地行号+页码，或 URL）、**最小争议命题一句话**、还缺什么证据才能判定、关联 GAP。

## 最要紧的两条（本工程直接相关）
- **K03（(9-1) 本身）**：LANA 直引两处（行 2138-2141 的目标表述；行 2274-2293 的评估），并明说
  "we, the LANA project, do not have a proof of (9-1)"、"unable to reach complete consensus"。这是 `SOURCE_FACT`。
- **K05（Cor 3.12 是争点）**：LANA 行 2283-2289 把"从 Theorem 3.11 推出 Cor 3.12 的过程"点名为**双方共同**的问题，
  且把它与"实线副本的识别"联系起来——与本工程 `GAP-core-comparison-reconstruction.md` 指向同一处。

## 证据分级（必须一起读）
- `SOURCE_FACT`：本地文本可复算的行号/页码（LANA 两处、LANA 的 SS 评估段）。
- `SECONDARY_DIGEST`：Scholze–Stix、Joshi、Dupuy–Hilado 的内容来自 2026-10-16 的摘录文件，**本地没有原文**，
  未逐字对校；引用具体句子前必须先取原文。
- `UNRESOLVED`：IUT IV Step (v) 的原文未在本地缓存中定位；Θ-link 是否必须是环同态一事文本两读皆通。

## 不做
不声称穷尽异议、不声称形成共识、不判定谁对；不做数学有效性审查。
"""
(N02 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md', LANA, DIGEST,
           'research/core-backward-2026-10-23/lana-report-assessment.md'] if (ROOT / p).exists()]
outputs = [{'path': rel(N02 / n), 'sha256': sha(N02 / n)} for n in
           ['SUMMARY.md', 'controversies.csv', 'notes.md', 'make_N02.py']]

delivery = {
    'task_id': 'N02',
    'status': 'STATIC_COMPLETE',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': LANA, 'line_or_page': '2274-2293 (p.49-50)',
         'supports': 'that the LANA assessment accepts the non-commuting diagram, points at (9-1), and states no proof of it exists'},
        {'path': LANA, 'line_or_page': '2283-2289 (p.49)',
         'supports': 'that the 3.11 -> 3.12 step and the identification of copies of R are named as the shared problem'},
    ],
    'commands_run': [
        'py -3 read-only extraction of LANA text with page markers (9.2, 10.5)',
        'py -3 read of research/controversies.md for the secondary source routes',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'Scholze-Stix / Joshi / Dupuy-Hilado 的原文本地没有，表中内容为二手摘录（SECONDARY_DIGEST），未逐字对校',
        'IUT IV Step (v) 的原文未定位，K08 无本地反引文',
        'Θ-link 是否必须是环同态：文本两读皆通，未裁决',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N02 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N02 written, rows', len(ROWS))
