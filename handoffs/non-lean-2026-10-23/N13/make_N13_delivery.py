import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N13 = ROOT / 'handoffs/non-lean-2026-10-23/N13'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


CARDS = [
    ('C1', 'candidates/core-transport/H3Synthesis.lean', 161, 163,
     'docstring: exponent_unique / reading R x != 0 called "exactly the non-torsion condition"',
     'wording_overclaim', 'SOURCE_FACT + JUDGEMENT',
     'for an arbitrary additive reading, non-vanishing != non-torsion; trivialReading + infinite-order probeOne is the counterexample shape',
     'say "non-vanishing reading" and state the injectivity hypothesis explicitly',
     'minimal hypothesis for the equivalence; check W9/W10 docstrings for the same wording'),
    ('C2', 'candidates/core-transport/ExponentUniqueness.lean', 288, 290,
     'exponent_determined quantifies over all x : Q_[3] while localLog is a tsum that is 0 when divergent',
     'vacuous_hypothesis_region', 'SOURCE_FACT + JUDGEMENT',
     'at probes where either side diverges both sides read 0, so the hypothesis holds automatically there',
     'restrict the hypothesis to the convergence region (or state it at x = 4, which is what the proof uses)',
     'no new mathematics needed; reuse power_reading_injective_on_probe'),
    ('C3', 'candidates/core-transport/LabelNormalization.lean', 165, 169,
     'averageOverLabels_eq_averageOverOrbit carries hAct : Bijective (fun g => g • base)',
     'conditional_identity_cited_flat', 'SOURCE_FACT + JUDGEMENT',
     'the file itself says the identity is deliberately weak and that hAct fails for the real normalisation; PATH.md:35 summarises W12 as a landing without hAct',
     'qualify PATH.md:35 as a conditional landing, or cite the file self-statement at LabelNormalization.lean:84',
     'index-level wording only'),
    ('C4', 'candidates/core-transport/EtaComparison.lean', 293, 296,
     'docstring of in_orbit_iff_exists_iso_in_family says the right-hand side is "not a mere restatement"',
     'self_assessment_overclaim', 'JUDGEMENT',
     'orbitFamily H c0 s = s • c0, so every member has the same orbit as c0; the equivalence is the definition unfolded',
     'drop the clause and call it a rewrite',
     'none (wording)'),
    ('C5', 'candidates/core-transport/TransitionCompatibility.lean', 632, 637,
     'four #print axioms lines duplicated (also at 593-596) under a comment claiming they were "absent from the report list"',
     'duplicated_receipt_and_false_comment', 'SOURCE_FACT',
     'the four lines are already part of 593-596; the file has 54 #print axioms lines with 4 duplicates, so the comment is false for the current file',
     'delete the duplicate block or rewrite the comment to "already covered above"',
     'check whether any downstream script parses this block by line number'),
    ('C6', 'candidates/core-transport/H3Synthesis.lean', 206, 217,
     'comparison_well_defined (hu : reading R u = 0) (hM : M != 0)',
     'checked_no_finding', 'SOURCE_FACT',
     'hu is an input condition and the file gives a numeric counterexample when it fails, so the conclusion is not hidden in the hypothesis',
     'none, but any downstream citation must carry hM : M != 0, otherwise the statement is false at M = 0',
     'carry hM through every restatement'),
]

rows = ['id,file,line_start,line_end,declaration,risk_kind,source_fact_vs_judgement,why,proposed_fix,needs']
for c in CARDS:
    rows.append(','.join('"' + str(x).replace('"', "'") + '"' for x in c))
(N13 / 'declarations.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

summary = """# N13 — 声明、假设与原文忠实性的静态审查

状态：`STATIC_COMPLETE`（风险清单；**不产生**任何形式化通过）

审查 5 个关键声明 + 1 处收据块，出 **6 张卡 + 1 项「未审」说明**（`risk-cards.md`，表在 `declarations.csv`）。
只读文本：未运行 Lean/Lake/LSP，未打开编辑器；五文件的 `sorry / axiom / set_option` 文本出现次数均为 0（`SOURCE_FACT`）。

## 三条最要紧的
1. **C1**：`H3Synthesis.lean:161-163` 把「读数非零」写成「exactly the non-torsion condition」。读数是**任意**加法读数，
   该等价只在读数于 `⟨x⟩` 上单射时成立；同一文件里的 `trivialReading`（全员读 0）与无限阶生成元 `probeOne`
   正好给出反例形状。建议改成「非零读数」并把单射条件写成假设。
2. **C2**：`ExponentUniqueness.lean:288-290` 的假设量化**全部** `ℚ_[3]`，而 `localLog` 是 `tsum`（不可和取 0，
   `CoreTransport/Basic.lean:9-10`）：在发散的探针处两边都是 0，假设自动成立。假设比字面读起来弱得多。
3. **C3**：`LabelNormalization.lean:165-169` 的恒等式**以 `hAct` 为假设**，文件自己在 `:84`、`:224` 说明了这一点；
   索引文件 `PATH.md:35` 却概括为「M-iii 落地」，丢了条件。

## 其余
- **C4**：`EtaComparison.lean:293-296` 自评「不是同义反复」不成立——`orbitFamily` 让每个成员的轨道都等于 `c₀` 的轨道。
- **C5**：`TransitionCompatibility.lean:634-637` 的 4 条 `#print axioms` 与 `:593-596` 重复，且 `:632-633` 的注释
  「absent from the report list」对当前文件为假（全文 54 条，4 条重复）。
- **C6**（已核、无问题）：`comparison_well_defined` 的 `hu` 是输入条件不是伪装结论；但 `hM : M ≠ 0` 必须随引用携带。

## 未审（`UNRESOLVED`）
Mathlib 侧声明、外部仓库 `Reconstruction/Cor312/Concrete`、以及任何 `#print axioms` 的真实依赖闭包都未审；
**静态「没发现问题」不等于形式化通过**，核心 GAP 保持 OPEN。
"""
(N13 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = []
for p in ['handoffs/non-lean-task-catalog-2026-10-23.md',
          'candidates/core-transport/H3Synthesis.lean',
          'candidates/core-transport/ExponentUniqueness.lean',
          'candidates/core-transport/LabelNormalization.lean',
          'candidates/core-transport/EtaComparison.lean',
          'candidates/core-transport/TransitionCompatibility.lean',
          'candidates/core-transport/CoreTransport/Basic.lean',
          'research/core-backward-2026-10-23/PATH.md']:
    inputs.append({'path': p, 'sha256': sha(ROOT / p)})

outputs = [{'path': rel(N13 / n), 'sha256': sha(N13 / n)} for n in
           ['SUMMARY.md', 'risk-cards.md', 'declarations.csv', 'make_N13_delivery.py']]

delivery = {
    'task_id': 'N13',
    'status': 'STATIC_COMPLETE',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'candidates/core-transport/TransitionCompatibility.lean', 'line_or_page': '593-596 versus 632-637',
         'supports': 'the duplicated receipt block and the false comment, both quotable in one diff'},
        {'path': 'candidates/core-transport/H3Synthesis.lean', 'line_or_page': '161-163 and 226-227',
         'supports': 'the "exactly the non-torsion condition" wording and the trivial reading that refutes it'},
    ],
    'commands_run': [
        'py -3 read-only line extraction (pathlib) over the five .lean files, to quote the exact lines',
        'Select-String "sorry|axiom|set_option" over the five files -> 0 matches each (text count only)',
        'Select-String "#print axioms" -> 54 lines in TransitionCompatibility.lean, 4 of them duplicated',
    ],
    'new_hypotheses': [],
    'unresolved': [
        '未重算任何 #print axioms 的真实依赖闭包；文本搜索不等于公理审计',
        '未审 Mathlib 与外部仓库（Reconstruction/Cor312/Concrete）侧声明',
        'C1/C2 的修订建议未编译；它们是需要后续形式化的提案，不是已完成修正',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N13 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N13 written, cards', len(CARDS))
