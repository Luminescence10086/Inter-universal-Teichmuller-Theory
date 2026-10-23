"""N03 -- build obligations.csv + SUMMARY.md + delivery.json for the target spec."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N03 = ROOT / 'handoffs/non-lean-2026-10-23/N03'
LANA = 'research/round2-source-cache/LANA-interim-report-2026-07.txt'
ETAALG = 'reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


OBL = [
    ('O1', 'construct a suitable S: exist S : Ind3 D with logVol(out iota S) = qPilot.lhs',
     'sufficient', ETAALG, '151', 'SOURCE_FACT',
     'the Lean statement turns (9-1) into this scalar equation, so a witness for the equation is a witness for (9-1)',
     'no witness exists in the repository; logVol of out is not computed for any constructed S'),
    ('O2', 'equality of the two maps is decided at the pilot',
     'necessary', 'reviews/core-round/external/iut/Iut/Wall/BPS.lean', '335 (eta_eq_eta_iff)',
     'SOURCE_FACT',
     'a map of pointed lines is determined by the image of the pilot, so eta_q = etaAnab_S iff they agree at the pilot',
     'nothing missing on this step; it is the reduction, not the content'),
    ('O3', 'the indeterminacies Ind1/Ind2 must be compatible with the chosen S',
     'necessary', LANA, '45-46 (lines 2117-2121)', 'SOURCE_FACT',
     'the report states the anabelian action is subject to Ind1 and Ind2, so S must be chosen inside a compatible class',
     'no formal statement of the compatibility condition on S; the Lean IndAut only names the acting sets'),
    ('O4', 'iota (the Choice) is fixed before S is quantified',
     'necessary', ETAALG, '151', 'SOURCE_FACT',
     'the Lean statement quantifies iota first and S second; the paper says "some suitable S" after fixing the data',
     'none; it is a quantifier-order fact, listed so that a future restatement does not swap them'),
    ('O5', 'invariance of the reading over the whole family is NOT required',
     'non-obligation', 'research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean',
     'existence_does_not_force_invariance', 'SOURCE_FACT',
     'existence of one S making the maps equal does not force invariance along the family; the earlier report '
     'wrongly treated W5/W7 invariance as necessary',
     'none; this row exists to stop the stronger condition being smuggled back in'),
    ('O6', 'the volume normalisation used by logVol must match the pilot normalisation of R^ss',
     'necessary', LANA, '46 (lines 2126-2137)', 'SOURCE_FACT',
     'the pilot of R^ss is the class of M = 1.S, while the pilot of eta_q is the class of {q_v O_v} embedded '
     'diagonally; comparing them presupposes one normalisation for both',
     'the normalisation ledger is N06; until it is done, O1 cannot even be posed precisely'),
    ('O7', 'dependence on the q-pilot left-hand side being the same object as the paper q',
     'necessary', ETAALG, '151', 'UNRESOLVED',
     'the Lean side compares against (concreteVariantData D).qPilot.lhs; that this field is the paper q is not '
     'established in the repository',
     'needs a source-level identification, not a Lean proof'),
    ('O8', 'Cor 3.12 needs (9-1) plus the xi-d..xi-f log-volume computations',
     'dependency', LANA, '49-50 (10.5)', 'SOURCE_FACT',
     'the report treats (9-1) as one step of the Cor 3.12 argument, not as its conclusion',
     'the other steps are separate open items; nothing here claims them'),
    ('O9', 'abc needs the Cor 3.12 arithmetic conclusion plus a height comparison',
     'dependency', LANA, '49-50 (10.5)', 'UNRESOLVED',
     'even with Cor 3.12 the passage to abc requires the arithmetic identification, which the report does not settle',
     'out of scope of this task; listed so that no reader infers abc from (9-1)'),
]

rows = ['id,obligation,kind,source_path,line_or_page,tag,why,status']
for o in OBL:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in o))
(N03 / 'obligations.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

summary = """# N03 — 核心目标的量词、类型与依赖清单

状态：`STATIC_COMPLETE`（目标规格草稿；不声称 (9-1) 成立）

## 一句话
(9-1) 是：**固定数据后，存在某个 `S : Ind3 D` 使 `etaAnab ι S = etaQ D`**；在 Lean 侧它等价于一个实数等式
`logVol(out ι S) = qPilot.lhs`。目标是存在型，不是全族不变型。

## 三条必须分开的条件（`obligations.csv` 有 9 行）
- **充分**：造出一个 `S` 使标量方程成立（O1）——仓库里**没有**这样的 `S`，`logVol(out ι S)` 从未对任何构造出来的 `S` 算出。
- **必要**：两图相等 ⟺ 在 pilot 处相等（O2，`eta_eq_eta_iff`）；`Ind1/Ind2` 相容（O3）；`ι` 先于 `S` 量化（O4）；
  两套 pilot 归一化必须对齐（O6，留给 N06）。
- **更强但非必需**：读数在整个族上不变（= W5/W7）。本工程已用 `existence_does_not_force_invariance` 证明它不被蕴含，
  写成它会把目标换成另一个问题（O5）。

## 到 Cor 3.12 / abc 的依赖
单列为 O8、O9：Cor 3.12 还需要 xi-d…xi-f 的 log-volume 计算；abc 还需要高度比较与算术识别。
**两条都不因 (9-1) 而成立**，本件不预设它们已完成。

## 出处
原文：`LANA-interim-report-2026-07.txt` §9.2，p.45–46，行 2138–2141（"there exists some suitable S such that η_q = η^anab_S"）。
Lean：`Iut/Wall/EtaAlg.lean:151`（`etaAnab_eq_etaQ_iff`）。全部为 `SOURCE_FACT`，除 O7/O9 标 `UNRESOLVED`。

## 未做
没有形式化 `R^ss` 的商结构，没有构造 `Ind3 D` 的元素，没有算出任何 `logVol`；`target.md` 是规格，不是证明。
"""
(N03 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md', LANA, ETAALG,
           'research/core-backward-2026-10-23/lana-report-assessment.md',
           'research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean']]
outputs = [{'path': rel(N03 / n), 'sha256': sha(N03 / n)} for n in
           ['SUMMARY.md', 'target.md', 'obligations.csv', 'make_N03.py']]

delivery = {
    'task_id': 'N03',
    'status': 'STATIC_COMPLETE',
    'source_commit': 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': LANA, 'line_or_page': 'lines 2138-2141 (p.45-46)',
         'supports': 'the goal is existential: "there exists some suitable S such that eta_q = eta_anab_S"'},
        {'path': ETAALG, 'line_or_page': '151',
         'supports': 'the Lean-side form: (9-1) iff logVol(out iota S) = qPilot.lhs'},
    ],
    'commands_run': [
        'py -3 read-only extraction of LANA text, locating 9.2 / 9.3 / 10.5 with page markers',
        'Select-String over the external repo for etaAnab_eq_etaQ_iff',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'O1 的见证不存在：没有任何构造出来的 S 与算出的 logVol',
        'O7：qPilot.lhs 是否就是原文的 q，仓库内未建立',
        'O9：Cor 3.12 到 abc 的算术识别未处理',
        '未形式化 R^ss 的商结构；target.md 只是规格',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N03 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N03 written, obligations', len(OBL))
