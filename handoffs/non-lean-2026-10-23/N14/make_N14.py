import hashlib
import json
import pathlib

ROOT = pathlib.Path(r'D:\Inter-universal Teichmüller Theory')
N14 = ROOT / 'handoffs/non-lean-2026-10-23/N14'
data = json.loads((N14 / 'audit-data.json').read_text(encoding='utf-8-sig'))


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


rows = ['task,receipt_path,receipt_sha256,target_file,target_sha256_now,source_sha_match,'
        'capture_after_source,tree_axiom_rows,tree_axiom_rows_of_own_file,declared_status,status,needed_action']
records = []
for r in data['records']:
    status = r['status']
    needed = r.get('needed_action') or ''
    # A receipt taken before the source file's last modification cannot attest the current source even when
    # the recorded hash happens to equal the present one: that is the STALE_HASH case, not INSUFFICIENT.
    if r.get('receipt_exists') and r.get('capture_after_source') is False:
        status = 'STALE_HASH'
        needed = ('re-capture after the current source hash; the existing capture predates the last '
                  'modification of the target file')
    records.append((r, status, needed))
    rows.append(','.join([
        r['task'],
        r.get('receipt_rel') or r.get('experimental_receipt_rel') or '',
        r.get('receipt_sha_now') or '',
        r.get('target_file') or '',
        r.get('target_sha256_now') or '',
        str(r.get('source_sha_match')),
        str(r.get('capture_after_source')),
        str(r.get('axiom_rows')),
        str(r.get('own_axiom_rows')),
        r.get('declared_status') or '',
        status,
        (needed or '').replace(',', ';'),
    ]))
(N14 / 'receipt-review.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

counts = {}
for _, s, _ in records:
    counts[s] = counts.get(s, 0) + 1
supported = [r['task'] for r, s, _ in records if s == 'SUPPORTED_BY_EXISTING_EVIDENCE']
must_recheck = [r['task'] for r, s, _ in records if s in ('INSUFFICIENT', 'STALE_HASH')]
missing = [r['task'] for r, s, _ in records if s == 'MISSING']

summary = f"""# N14 — 既有编辑器收据的静态证据分级

状态：`STATIC_COMPLETE`（分级表；本任务**不**产生任何编辑器准入）

## 判据
只看既有文件：收据是否指向**该任务自己的绝对路径**、源码哈希是否与当下文件一致、时间顺序（抓取是否晚于源码最后修改）、
树里是否有**该文件自身**的公理行/目标证据、以及"窗口级没有问题"和"指定文件实际完成验证"的区分。
别的文件的公理行不计入本文件证据；行数只是线索。

## 结果（{len(records)} 项）
- `SUPPORTED_BY_EXISTING_EVIDENCE`：{counts.get('SUPPORTED_BY_EXISTING_EVIDENCE', 0)} 项 —— {', '.join(supported) or '无'}
- `INSUFFICIENT`：{counts.get('INSUFFICIENT', 0)} 项
- `STALE_HASH`：{counts.get('STALE_HASH', 0)} 项 —— {', '.join([r['task'] for r, s, _ in records if s == 'STALE_HASH']) or '无'}
- `MISSING`：{counts.get('MISSING', 0)} 项 —— {', '.join(missing) or '无'}

## 必须补做编辑器验证的项目
{', '.join(must_recheck + missing) if (must_recheck or missing) else '无'}

## 关键发现
1. **只有 6 项的既有证据真正指向本文件**：K4、W2、W3、W5、W6、T3。其余任务的树里出现的公理行属于**同窗口的其它文件**。
2. **W9、W10 的抓取时间早于其源码的最后修改**（R2 改了源件）——即使记录里的哈希与当下一致，那份收据也不能担保现在的源码，
   因此判 `STALE_HASH`，不是 `INSUFFICIENT`。
3. M1–M4、T1、T2、T4 没有编辑器收据（`STATIC_ONLY` 或 `EDITOR_PENDING`），判 `MISSING`；`T4` 声明了 `EDITOR_PENDING` 也一样没有文件。
4. W1、W4、W7、W8、W11、W12 有收据但树里**没有本文件的公理行**，判 `INSUFFICIENT`：这与此前 R3 对 W8/W9/W11 的降级结论一致。

## 边界
本任务不打开编辑器、不启动 Lean，不给自己填任何 editor PASS；`editor_run=false`。分级只说明"现有文件够不够支撑该声明"，
不说明这些 Lean 文件在编辑器里现在是否有诊断。
"""
(N14 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': rel(ROOT / 'handoffs/core-backward-2026-10-23/fix-delivery.json'),
           'sha256': sha(ROOT / 'handoffs/core-backward-2026-10-23/fix-delivery.json')}]
for r in data['records']:
    for key in ('delivery_rel',):
        if r.get(key):
            p = ROOT / r[key]
            if p.exists():
                inputs.append({'path': r[key], 'sha256': sha(p)})
outputs = [{'path': rel(N14 / n), 'sha256': sha(N14 / n)} for n in
           ['SUMMARY.md', 'receipt-review.csv', 'audit_n14.py', 'audit-data.json', 'audit-detail.txt', 'make_N14.py']]

delivery = {
    'task_id': 'N14',
    'status': 'STATIC_COMPLETE',
    'source_commit': data['git_head'],
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N14/audit-detail.txt', 'line_or_page': 'K4 block',
         'supports': 'a worked example of the grading: own axiom rows present, capture after source, hash match'},
        {'path': 'handoffs/non-lean-2026-10-23/N14/receipt-review.csv', 'line_or_page': 'rows W9 and W10',
         'supports': 'the STALE_HASH verdict, with capture_after_source=false and the matching hash recorded'},
    ],
    'commands_run': [
        'py -3 handoffs/non-lean-2026-10-23/N14/audit_n14.py  (read-only audit of every delivery + receipt)',
        'py -3 handoffs/non-lean-2026-10-23/N14/make_N14.py   (CSV and JSON assembly)',
        'py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py --only N14',
    ],
    'new_hypotheses': [],
    'unresolved': [
        '本任务不能完成编辑器准入：所有 INSUFFICIENT / STALE_HASH / MISSING 项都需实际编辑器补验',
        'T3 的 source_sha_match 为 None（其 delivery 未记录源码哈希），因此对 T3 的判定只依据树内本文件公理行与路径',
        'W9/W10 的抓取时间与源码修改时间的先后依据文件 mtime，不是仓库提交时间；若有人手工改回 mtime 结论会变',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N14 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N14 written', counts, 'supported:', supported)
