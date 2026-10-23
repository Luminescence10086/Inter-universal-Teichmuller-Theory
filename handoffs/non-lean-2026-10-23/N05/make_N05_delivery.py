import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N05 = ROOT / 'handoffs/non-lean-2026-10-23/N05'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


inputs = []
for p in ['handoffs/non-lean-task-catalog-2026-10-23.md',
          'handoffs/core-integral-source-2026-10-23.md',
          'research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt',
          'reviews/core-round/external/iut/Iut/Concrete/LocalConstruct/IndAut.lean',
          'reviews/core-round/external/iut/Iut/Concrete/LocalConstruct/LogShell.lean',
          'reviews/core-round/external/iut/Iut/Concrete/LocalConstruct/Integral.lean']:
    if (ROOT / p).exists():
        inputs.append({'path': p, 'sha256': sha(ROOT / p)})

outputs = [{'path': rel(N05 / n), 'sha256': sha(N05 / n)} for n in
           ['SUMMARY.md', 'evidence.csv', 'verify_N05.py', 'verify-report.json',
            'fix_N05_hashes.py', 'hash-corrections.json', 'make_N05_delivery.py']]

delivery = {
    'task_id': 'N05',
    'status': 'STATIC_COMPLETE',
    'source_commit': 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N05/evidence.csv', 'line_or_page': 'row N05-01 (Ob1, p.131, lines 8033-8036)',
         'supports': 'that the passage denies O×-stability of the log-shell I_k, so no preserved lattice can be filled in'},
        {'path': 'handoffs/non-lean-2026-10-23/N05/evidence.csv', 'line_or_page': 'row N05-11 (IndAut.indAut, lines 299-301)',
         'supports': 'what the Lean side actually preserves (⊗_j K_{c j} as a set equality) versus the paper\'s (Ind3)'},
    ],
    'commands_run': [
        'py -3 handoffs/non-lean-2026-10-23/N05/verify_N05.py  -> ALL_QUOTES_VERIFIED (11/11 rows)',
        'py -3 handoffs/non-lean-2026-10-23/N05/fix_N05_hashes.py -> corrected 3 input_sha256 values',
        'py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py --only N05',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'shared_finite_quotient 整列 UNRESOLVED：原文与源码都没有"共用同一个有限商"的陈述；唯一被命名的商是 log-volume 商（非有限）',
        'Ind1/Ind2 两行整体 UNRESOLVED：原文只说明"什么在作用"，没有说明保持了哪个结构',
        '未读 ArchIndAut.lean；Ind3 在 Lean 侧没有对应对象',
        '本件是来源台账，不判定原文忠实性，也不判定任何命题真假',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N05 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N05 delivery written; inputs', len(inputs))
