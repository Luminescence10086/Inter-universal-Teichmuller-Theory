"""N08 -- lemmas.csv + SUMMARY.md + delivery.json."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N08 = ROOT / 'handoffs/non-lean-2026-10-23/N08'
GAPDOC = 'GAP-core-residue-hull-realization.md'
RES = 'research/residue-hull-2026-10-23.md'
PRIN = 'research/principal-hull-2026-10-23.md'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


ROWS = [
    ('L1', 'finite index between the reference lattice and O^n gives the volume conversion',
     'K/Q_p finite; O its ring of integers; Lambda an O-lattice with O^n and Lambda mutually contained in K^n',
     'vol_Lambda = [O^n : Lambda] * vol_{O^n} under one Haar measure',
     'Hecke index formula + multiplicativity of Haar measure over a finite-index subgroup; O is Z_p-free of rank [K:Q_p]',
     'Lambda only K-isomorphic to O^n with infinite index: the factor is then infinite and no conversion exists',
     'does III Remark 3.9.5(i) fix the reference lattice at all? if not, this hypothesis is mine and must be labelled new',
     'UNVERIFIED_MATH'),
    ('L2', 'the common container is A + B, and it need not be of the form lambda*O for n >= 2',
     'A, B are O-lattices in K^n',
     'the least O-lattice containing both is A+B, which is free over the DVR O',
     'A+B contains both; any O-submodule containing both contains A+B; over a DVR submodules of K^n are free',
     'for n >= 2, A+B is in general NOT of the form lambda*O^n, so "the container is lambda*O" needs an extra hypothesis',
     'is the paper lambda*O componentwise (lambda = (lambda_i), each nonzero) or a single element?',
     'UNVERIFIED_MATH'),
    ('L3', 'the pulled-back container equals the original hull exactly when no component collapses',
     'n >= 1; lambda = (lambda_1,...,lambda_n) with every component nonzero; hull := prod_i lambda_i O; C a pulled-back container',
     'C = hull iff the projection of C to every component is lambda_i O',
     'forward from C subset hull plus equality of free ranks; backward by comparing generators componentwise',
     'if some lambda_i = 0 the pulled-back container degenerates and the two sides differ in rank',
     'quote the sentence in III Remark 3.9.5(i) that excludes zero components, so the condition is sourced',
     'UNVERIFIED_MATH'),
    ('L4', 'normalised volume of the container against the original log-volume',
     'L1 index I finite; Haar measure mu with mu(O^n) = 1',
     'vol_orig(lambda O^n) = -log_p |I| - sum_i log_p |lambda_i|_p after aligning mu with the original log-volume',
     'multiplicativity gives mu(lambda O^n) = prod |lambda_i|_p; the index correction |I|_p comes from L1',
     'the original log-volume need not use the same normalisation; a non-p-power discrepancy introduces an irrational factor (same gap as N06-10)',
     'which lattice has measure 1 in the original log-volume definition?',
     'UNVERIFIED_MATH'),
    ('L5', 'all allowed changes descend to one finite quotient',
     'every allowed change maps the reference lattice O^n to itself, i.e. G <= Aut(O^n)',
     'G acts on O^n/p^k O^n and this action is compatible with the action on the container',
     'well-definedness from preserving p^k O^n; compatibility because the action commutes with inclusion',
     'N05 records shared_finite_quotient as UNRESOLVED for every paper item; if some allowed change does not preserve the lattice, the hypothesis fails',
     'III 3.11 Ind1/Ind2/Ind3: is there any source sentence saying they preserve one finite quotient?',
     'UNRESOLVED'),
]

rows = ['id,lemma,statement,hypotheses,proof_draft,possible_failure,needed_source_evidence,tag']
for r in ROWS:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in r))
(N08 / 'lemmas.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

summary = """# N08 — 原始 hull 与现有主格工具的接合草稿

状态：`STATIC_COMPLETE`（证明计划；5 条引理全部 `UNVERIFIED_MATH`，一条都未形式化）

## 起点/终点
- 起点：`PrincipalProduct.lean`、`PadicPrincipalHull.lean` 在**模型** `ℚ_p^n / ℤ_p^n` 上的六条结果（紧性、正体积、
  Haar 计数、共同容器、最小主核性）。
- 终点：把它接到原文 `λ·O_{F_v}` 的原始允许 hull，并把参考格体积换算到原始 log-volume。
- 中间的四条未实化义务取自 `GAP-core-residue-hull-realization.md`；本计划把前三条落成 L1–L3、第四条落成 L4，
  另加 L5（所有允许变化是否落到同一个商上）。

## 五条引理里最要紧的一条
**L2 的失败例**：`n ≥ 2` 时两个格的共同容器 `A+B` **一般不是** `λ·O^n` 形。所以"容器是 `λ·O` 型"这一点
在模型层（`n = 1`）自动，在真实情形**不自动**——任何把模型直觉外推的写法都会在这里断掉。

## 与既有结果的关系
模型层的六条结论对应 L1–L3 的**模型特例**（参考格就是 `ℤ_p^n`、且 `n = 1` 时全部成立）。
剩下要补的是 `n ≥ 2` 与真实 `O_{F_v}` 两层，以及 L4 的归一化与 L5 的商作用。

## 明确不做
不声称原文 hull 估计成立、不推出 Cor 3.12 或 abc；L1/L3/L4 的关键条件是否**有原文支持**目前未知，
若原文没有，那些条件必须标成我新增的假设（这也是本计划 `needed_source_evidence` 列的用途）。
"""
(N08 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md', GAPDOC,
           'handoffs/non-lean-2026-10-23/N06/normalizations.csv',
           'handoffs/non-lean-2026-10-23/N05/evidence.csv'] if (ROOT / p).exists()]
outputs = [{'path': rel(N08 / n), 'sha256': sha(N08 / n)} for n in
           ['SUMMARY.md', 'bridge-plan.md', 'lemmas.csv', 'make_N08.py']]

delivery = {
    'task_id': 'N08',
    'status': 'STATIC_COMPLETE',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N08/lemmas.csv', 'line_or_page': 'row L2',
         'supports': 'the failure example that kills the naive transfer of the model container to n >= 2'},
        {'path': 'handoffs/non-lean-2026-10-23/N08/lemmas.csv', 'line_or_page': 'row L5',
         'supports': 'that the shared-finite-quotient hypothesis has no source support yet (N05 records UNRESOLVED)'},
    ],
    'commands_run': [
        'py -3 read-only line extraction of GAP-core-residue-hull-realization.md',
        'cross-read of N05/evidence.csv (shared_finite_quotient column) and N06/normalizations.csv',
    ],
    'new_hypotheses': [
        'L1 的"参考格与 O^n 互相包含"是我加的假设，未在原文中核到（需要 III Remark 3.9.5(i) 原文核对）',
        'L3 的"每分量非零"在模型层不成立，作为原始情形的条件需要原文引文支撑',
    ],
    'unresolved': [
        '五条引理均未形式化；L5 的假设目前无来源支持',
        'L4 与 N06-10 同源：两套 log 之间没有比较映射',
        'n >= 2 的共同容器形状与原文 λ·O 的关系未定',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N08 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N08 written, lemmas', len(ROWS))
