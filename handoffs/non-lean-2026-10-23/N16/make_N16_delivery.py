import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N16 = ROOT / 'handoffs/non-lean-2026-10-23/N16'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


inputs = [{'path': 'handoffs/non-lean-task-catalog-2026-10-23.md',
           'sha256': sha(ROOT / 'handoffs/non-lean-task-catalog-2026-10-23.md')}]
# `report-snapshot.json` is deliberately NOT declared as an output: it records the state of the package at
# the moment it was produced, so hashing it inside the same package would create a fixed-point problem (the
# report would have to describe a delivery that hashes the report). It is kept as evidence of one real run.
outputs = [{'path': rel(N16 / n), 'sha256': sha(N16 / n)} for n in
           ['SUMMARY.md', 'check_deliveries.py', 'make_N16_delivery.py']]

delivery = {
    'task_id': 'N16',
    'status': 'STATIC_COMPLETE',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N16/check_deliveries.py',
         'line_or_page': 'check_task(): the outputs/inputs hash loops',
         'supports': 'that every declared hash is recomputed from disk rather than trusted'},
        {'path': 'handoffs/non-lean-2026-10-23/N16/report.json', 'line_or_page': 'selftest array',
         'supports': 'the five fixture rejections, with the exact error text each one produced'},
    ],
    'commands_run': [
        'py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py --selftest --json-out report.json',
        'py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py   (full package, exit 1 while tasks are missing)',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'CSV 语义不校验（列含义、引文忠实性需任务专属校验器，例如 N05/verify_N05.py）',
        '不检查交付之间的一致性与冲突（属 N15 索引层）',
        '工具只做工程校验，不构成数学验收',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N16 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N16 delivery written')
