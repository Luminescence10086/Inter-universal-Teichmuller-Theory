"""N06 -- build normalizations.csv, SUMMARY.md and delivery.json."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N06 = ROOT / 'handoffs/non-lean-2026-10-23/N06'
LANA = 'research/round2-source-cache/LANA-interim-report-2026-07.txt'
III = 'research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt'
LAB = 'candidates/core-transport/LabelNormalization.lean'
CORE = 'candidates/core-transport/CoreTransport/Basic.lean'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


ROWS = [
    # id, from, to, formula_draft, conditions, source_path, line_or_page, missing_link, gain_loss, tag
    ('N06-01', 'pilot of R^ss (class of M = 1·S)', 'pilot of eta_q (class of {q_v O_v} embedded diagonally)',
     'pilot_q = c · pilot_S for a single real constant c, with c fixed by the chosen volume normalisation',
     'the volume functional vol on V^C(I_v) must be the same on both sides; c must not depend on S',
     LANA, '2126-2137 (p.46)', 'the paper states the two pilots separately and never names c; no source fixes it',
     'if c exists and is independent of S, (9-1) reduces to one scalar equation; if c depends on S, the reduction is void',
     'UNVERIFIED_MATH'),
    ('N06-02', 'volume container V^C(I_v)', 'quotient R^ss',
     'R^ss = {T ⊂ V^C(I_v) adelic, measurable} / (vol T = vol T\')',
     'vol must be countably additive on the admissible T; the class must be independent of representatives',
     LANA, '2126-2127 (p.46)', 'which Haar normalisation defines vol is not stated in the retrieved text',
     'the quotient forgets shape and keeps volume only: every later comparison is a comparison of numbers',
     'UNVERIFIED_MATH'),
    ('N06-03', 'choice S ⊂ V^C(I_v)', 'the class M = 1·S with 1 ∈ N',
     'M = 1·S, pilot := class of M',
     'the action of N on V^C(I_v) must be defined and 1 must act as the identity on the pilot',
     LANA, '2127-2129 (p.46)', 'the relation between the N-action and the Ind1/Ind2 indeterminacies is not stated',
     'gives the pilot a name but not a value: nothing here pins the resulting real number',
     'UNVERIFIED_MATH'),
    ('N06-04', 'local data {q_v O_v} for v ∈ V', 'the single real line R^ss',
     'vol({q_v O_v}) = Σ_v w_v · log ‖q_v‖_v for weights w_v',
     'finiteness of the sum; w_v must be the same weights used in the global log-volume of IUT III',
     III, '11600-11654 (p.194, Remark 3.12.2(v))',
     'the weights w_v are the missing object: the retrieved passage names O×-indeterminacy, not a weight system',
     'without w_v the local-to-global step is a formula with a free parameter',
     'UNVERIFIED_MATH'),
    ('N06-05', 'average over the label set |F_l|', 'average over the orbit of the base label',
     'averageOverLabels = averageOverOrbit provided g ↦ g • base is bijective',
     'hAct : Function.Bijective (fun g => g • base), i.e. the label set IS the orbit',
     LAB, '165-169 (with the self-statement at 84 and 224)', 'none in the toy; the paper-side label set is not shown to be an orbit',
     'the identity is conditional: applied without hAct it is false (counterexample in the same file)',
     'SOURCE_FACT'),
    ('N06-06', 'zero label vs non-zero label', 'the two normalisations disagree',
     'with labels {0,1,2} and orbit {0}: averages are 2 vs 1 (ZMod 3 toy)',
     'this is the counterexample to dropping hAct; it is not a claim about the paper',
     LAB, '322-340 (anti-degeneracy block)', 'which paper-side normalisation corresponds to a "zero label" is not identified',
     'shows the failure is real, at explicit numbers, not merely formal',
     'EXPERIMENTAL'),
    ('N06-07', 'sum over group elements', 'sum over the orbit',
     'Σ_{g∈G} f(g • base) = #Stab · Σ_{orbit} f',
     'finite G; Stab the stabiliser of base; f invariant on the orbit',
     LAB, '147-157 (card_eq_card_of_bijective, sum_over_labels_eq_sum_over_orbit)',
     'the stabiliser multiplicity factor is absent from the paper side; no source fixes it',
     'gives the exact multiplicity: any average that ignores #Stab is off by that factor',
     'UNVERIFIED_MATH'),
    ('N06-08', 'Haar measure on Q_p^n / Z_p^n', 'Haar measure on the real coefficient ring O_{F_v}',
     'vol_naive(S) = [O_{F_v} : Z_p^n] · vol_model(S) once an identification is chosen',
     'the index must be finite; the identification must respect the lattice, not only the vector-space structure',
     'candidates/core-transport/CoreTransport/../PadicPrincipalHull.lean', 'declaration text only (no line numbers claimed)',
     'the repository has the model lattice only; N04 found no ring-level identification',
     'a finite index would make the conversion exact; nothing in the sources supplies that index',
     'UNRESOLVED'),
    ('N06-09', 'finite quotient counting', 'the counts entering the average',
     '#(O/p^k O) = p^{k·[K:Q_p]} for the model ring',
     'the ring must be the model Z/(p^k); for the real order the count is not this formula',
     III, 'p.131 block (lines 8020-8041) as the O×-indeterminacy context',
     'which family of finite quotients the paper uses is not determined (N04: no Finite (Tensor …) in the repo)',
     'the toy count is exact; its transfer to O_{F_v} is not established',
     'EXPERIMENTAL'),
    ('N06-10', 'p-adic log localLog (a Q_p-valued tsum)', 'real log-volume logVol(R)',
     'logVol = λ ∘ localLog for a comparison map λ : Q_p → R; no such λ exists as a field map',
     'λ would have to be additive on a subgroup and compatible with the norm; Q_p has no embedding into R',
     CORE, '9-10 (definition of localLog)', 'the two logarithms live in different fields; the repository contains no bridge',
     'unless a bridge is supplied, every "logVol = log" step is a change of objects, not an equality',
     'UNRESOLVED'),
]

rows = ['id,from_object,to_object,formula_draft,conditions,source_path,line_or_page,missing_link,gain_loss,tag']
for r in ROWS:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in r))
(N06 / 'normalizations.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

summary = """# N06 — 归一化、平均与体积换算台账

状态：`STATIC_COMPLETE`（换算条件草稿；公式全部 `UNVERIFIED_MATH`，算例 `EXPERIMENTAL`）

## 10 行台账（`normalizations.csv`）最要紧的三条
1. **两套 pilot 之间缺一个常数 `c`**（N06-01）：`R^ss` 的 pilot 是 `M = 1·S` 的类，`η_q` 的 pilot 是 `{q_v O_v}` 对角嵌入的类。
   原文从没给出两者的换算因子；`c` 若存在且与 `S` 无关，(9-1) 才化归为一条标量方程。**这是 N03 的 O6 那一行的展开。**
2. **局部→全局缺权重 `w_v`**（N06-04）：`vol({q_v O_v}) = Σ_v w_v log‖q_v‖_v`；检索到的段落只讲 `O×` 不确定，没有给权重系统。
   没有 `w_v`，"局部到全局"就是一个带自由参数的公式。
3. **两套 log 之间根本没有桥**（N06-10）：`localLog` 取值在 `ℚ_p`（`CoreTransport/Basic.lean:9-10`），`logVol` 取值在 `ℝ`；
   `ℚ_p` 没有到 `ℝ` 的域嵌入。任何"log 相等"的写法都必须先给出一层比较映射，否则是换了对象。

## 已能引用的正面结论
- `averageOverLabels_eq_averageOverOrbit` **以 `hAct` 为假设**（`LabelNormalization.lean:165-169`，文件自述 `:84`、`:224`）；
  去掉 `hAct` 由同一文件的 `ZMod 3` 反例给出 2 vs 1（N06-06）。这两行是 `SOURCE_FACT` / `EXPERIMENTAL`，不是 `UNVERIFIED_MATH`。
- 稳定子重数 `Σ_{g∈G} f(g•base) = #Stab · Σ_{orbit} f`（N06-07）在玩具里已证；缺的是原文侧是否有对应因子。

## 未做 / 明确留白
- 没有算出任何 `logVol(out ι S)`；N06 只是把该算的东西列出来。
- `PadicPrincipalHull` 一行的行号未声称（只给声明文本），因为该文件的声明位置本轮未逐行核对。
- 不把浮点近似当恒等式；本表没有给出任何数值"验证"。
"""
(N06 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md', LANA, III, LAB, CORE] if (ROOT / p).exists()]
outputs = [{'path': rel(N06 / n), 'sha256': sha(N06 / n)} for n in
           ['SUMMARY.md', 'notes.md', 'normalizations.csv', 'make_N06.py']]

delivery = {
    'task_id': 'N06',
    'status': 'STATIC_COMPLETE',
    'source_commit': 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': LANA, 'line_or_page': '2126-2137 (p.46)',
         'supports': 'that the two pilots are defined separately and no conversion constant is named (N06-01, N06-02)'},
        {'path': LAB, 'line_or_page': '165-169',
         'supports': 'that the label/orbit average identity carries hAct, and is therefore conditional (N06-05)'},
    ],
    'commands_run': [
        'py -3 read-only extraction of the LANA and IUT III texts around the cited line ranges',
        'py -3 (pathlib) line extraction from LabelNormalization.lean and CoreTransport/Basic.lean',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'N06-08 行未给 PadicPrincipalHull 的精确行号（只声明文本），需 N04 类逐行核对补上',
        'N06-10：两套 log 之间的比较映射在仓库中不存在，属结构性缺口',
        '全部公式是 UNVERIFIED_MATH 草稿；本任务不产生任何恒等式',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N06 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N06 written, rows', len(ROWS))
