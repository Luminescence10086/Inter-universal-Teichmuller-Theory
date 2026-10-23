"""N07 -- witness-contract.csv, SUMMARY.md, delivery.json."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N07 = ROOT / 'handoffs/non-lean-2026-10-23/N07'
LANA = 'research/round2-source-cache/LANA-interim-report-2026-07.txt'
ETA = 'reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean'
IND3 = 'reviews/core-round/external/iut/Iut/Wall/Ind3.lean'
RSS = 'reviews/core-round/external/iut/Iut/Wall/Rss.lean'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


ROWS = [
    ('W1', 'input BPS B (q-BPS of h2)', 'R^val with canonical pilot + etale-unit portion', LANA,
     '2142-2149 (p.46)', 'none', 'present in repository (external Iut/Wall)', 'yes', ''),
    ('W2', 'B, h1', 'a Theta-pilot identification iota : Iso B (thetaBPS h1)', ETA,
     '141 (abbrev Choice)', 'shared with W3 (iota and S are quantified together)', 'present', 'yes', ''),
    ('W3', 'D', 'an (Ind3)-choice S : Ind3 D', IND3,
     '213 (Ind3 := {S // IsAdelic D S and forall i, S i <= hullOf (vcI D) i})',
     'shared with W2', 'present as a subtype', 'yes',
     'the constraint chain S i <= hullOf is an upper bound, not a construction of S'),
    ('W4', 'iota, S', 'the output region LGP.S = out iota S', ETA,
     '105-109 (field out) + 143-147 (etaAnab uses logVol (out iota S))',
     'none', 'MISSING: out is a bare field, no implementation', 'NO',
     'this is the one arrow the whole task is about'),
    ('W5', 'out iota S', 'logVol (out iota S) : R', RSS,
     '453 (Rss.logVol)', 'none', 'partial: computed only for toy regions', 'partial',
     'needs the normalisation ledger N06-01/N06-04 before it is the paper quantity'),
    ('W6', 'logVol (out iota S), qPilot.lhs', '(9-1) for (iota,S)', ETA,
     '151-153 (etaAnab_eq_etaQ_iff)', 'none', 'present (the equivalence is proved)', 'yes',
     'the equivalence does not produce a solution; it only relocates the question'),
    ('W7', 'any alpha : EtUnitIso B.et B.et', 'a tau : Ind3 D =~ Ind3 D with out (alpha.trans iota) S = out iota (tau S)',
     ETA, '112-114 (ind12_acts_on_S)', 'shared with W3 via the induced tau', 'present as an existential', 'yes',
     'tau is not given by a formula, so compatibility of a concrete S cannot be checked'),
    ('W8', 'out iota S', 'IsAdelic D (out iota S) and InHullOfImage D (out iota S)', ETA,
     '123-125 (realisation, T3)', 'none', 'present as a property', 'yes',
     'a landing condition: it constrains out, it does not construct it'),
    ('W9', 'the whole pipeline', 'the joint witness: one iota and one S satisfying W3+W7+W6 simultaneously',
     LANA, '2138-2141 (p.45-46)', 'all of W2, W3, W7', 'MISSING', 'NO',
     'no instance: the repository has no constructed S, no computed out, no compatible tau'),
    ('W10', 'toy instance (H = top, c0 = 1, q = 4)', 'a genuine existence witness in the toy layer only',
     'candidates/core-transport/EtaComparison.lean', 'nine_one_at_four',
     'none', 'present', 'yes but not for the real objects',
     'unmet real conditions: S is a unit in R^x not an Ind3 element; no out/BPS/logVol; q != qPilot.lhs; no Ind1/Ind2'),
]

rows = ['id,step,input,output,rule_source_path,line_or_page,choice_shared_with,status,implemented_now,missing_condition']
for r in ROWS:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in r))
(N07 / 'witness-contract.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

summary = """# N07 — 原始合法输出的构造流程与联合见证

状态：`STATIC_COMPLETE`（构造规格 + 缺口清单；**没有任何一步被实现**）

## 一句话
`out` 在 Lean 侧是**裸字段**（`Iut/Wall/EtaAlg.lean:108-109`），所以"跑一遍 η-算法得到 `LGP·S`"这件事
在仓库里**不存在**。`realisation`（T3，`:123-125`）是落点条件（adelic + 落在某个 (Ind1)-像的全纯包络内），
不能反过来产生 `out`。整条执行链缺的那一条箭头就是"从 `(ι,S)` 到区域"这一步。

## 7 步流程与四层区分（`pipeline.md`）
流程：输入 BPS → 选 `ι`（`EtaAlg:141`）→ 选 `S : Ind3 D`（`Ind3.lean:213`）→ **跑算法得 `out ι S`（缺）**
→ 取 `logVol`（`Rss.lean:453`）→ 与 `qPilot.lhs` 比较（`EtaAlg:151-153`）→ 对 `(ι,S)` 得到 (9-1)。
四层：裸字段（`out`）/ 约束（`realisation`）/ 存在性证明（`ind12_acts_on_S`、`etUnitOnly`）/ 实际构造（⊥）。

## 三处协同缺口
- **G1 构造**：没有 `out` 的实现；M3 的接口审计里 11 个核心接口的 F3（合法执行）全为假。
- **G2 不确定性作用**：`ind12_acts_on_S` 只给"存在 `τ`"，没有公式，所以某个 `S` 是否相容无法判定。
- **G3 归一化**：`logVol` 与 `qPilot.lhs` 只有在两套 pilot 对齐后才是同一个量（N06-01/N06-04）。

## 最小拟议实例及其未满足条件
玩具层的 `nine_one_at_four`（`H = ⊤`、`c₀ = 1`、`q = 4`）确实存在见证，但它不在真实对象上：
`S` 不是 `Ind3` 元素、没有 `out/BPS/logVol`、`q` 与 `qPilot.lhs` 无关、没有 `(Ind1)/(Ind2)` 相容性（5 条全部列出）。

## 边界
不声称任何"合法执行"存在；不把分别存在的 `ι`、`S`、`τ` 拼成联合见证；`witness-contract.csv` 的 10 行里
有 3 行状态为 `MISSING/NO`，这就是当前的真实进度。
"""
(N07 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md', LANA, ETA, IND3, RSS,
           'candidates/core-transport/EtaComparison.lean']]
outputs = [{'path': rel(N07 / n), 'sha256': sha(N07 / n)} for n in
           ['SUMMARY.md', 'pipeline.md', 'witness-contract.csv', 'make_N07.py']]

delivery = {
    'task_id': 'N07',
    'status': 'PARTIAL',
    'source_commit': 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': ETA, 'line_or_page': '105-109 and 123-125',
         'supports': 'that out is a bare field and realisation is a landing condition, not a construction'},
        {'path': IND3, 'line_or_page': '213',
         'supports': 'that an Ind3 choice is a subtype with an upper-bound condition, so S is constrained but not built'},
    ],
    'commands_run': [
        'py -3 read-only grep over the external Iut/Wall files for out / Ind3 / Rss.logVol / etaAnab',
        'py -3 line extraction for the cited ranges',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'W4（产出区域）没有实现：out 是字段，不是算法',
        'W7 的 tau 没有公式，相容性无法判定',
        'W9 联合见证不存在',
        'W10 只是玩具见证，5 条真实条件全部未满足',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N07 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N07 written, rows', len(ROWS))
