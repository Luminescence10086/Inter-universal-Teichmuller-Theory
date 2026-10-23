"""Standalone static checker for a non-Lean delivery package (N16).

What it is: a read-only工程校验 entry for the package produced under
`handoffs/non-lean-2026-10-23/`. It answers one question only -- are the fixed inputs and the declared
outputs real, are the hashes true, does every `delivery.json` satisfy the public contract of
`handoffs/non-lean-task-catalog-2026-10-23.md` section 3, and does any delivery claim a verification it
was forbidden to perform. It is NOT a mathematical acceptance and it cannot close a GAP.

What it refuses to do:
  * it never executes anything inside the package (no scripts, no hooks, no Lean, no Lake);
  * it never trusts a self-declared hash -- every hash is recomputed from disk;
  * it never turns "no warning observed" into "verified".

Usage:
    py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py            # check the package
    py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py --json-out report.json
    py -3 handoffs/non-lean-2026-10-23/N16/check_deliveries.py --selftest # prove it rejects bad input

Exit codes: 0 all tasks clean, 1 findings present, 2 the checker itself could not run.
"""
import argparse
import copy
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

STATUSES = {"STATIC_COMPLETE", "EXPERIMENTAL", "PARTIAL", "UNRESOLVED", "INPUT_DRIFT"}
REQUIRED_KEYS = ["task_id", "status", "source_commit", "inputs", "outputs", "review_anchors",
                 "commands_run", "new_hypotheses", "unresolved", "lean_run", "editor_run",
                 "native_iut_realized", "fact_tree_admitted"]
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
# These tasks were forbidden to run Lean or take editor evidence; a delivery that claims either is a
# contract violation even when the hash bookkeeping is clean. The patterns are deliberately narrow:
# a sentence like "本任务不做编辑器验证" must not be flagged, only an actual claim of a pass.
FORBIDDEN_CLAIMS = [
    (re.compile(r'EDITOR_CHECKED|EDITOR_VERIFIED|editor[ _-]?PASS\b', re.I), 'claims an editor verdict'),
    (re.compile(r'axiom closure (?:verified|audited)|公理闭包(?:已验|已审)', re.I), 'claims a fresh axiom-closure audit'),
    (re.compile(r'fact[- ]tree (?:node )?(?:admitted|准入)|已准入 fact', re.I), 'claims fact-tree admission'),
]


def sha256(path):
    import hashlib
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def safe_rel(root, value):
    """Return (ok, note): the path must be relative, must not escape the repo root."""
    if not isinstance(value, str) or not value:
        return False, 'not a non-empty string'
    p = Path(value)
    if p.is_absolute() or re.match(r'^[A-Za-z]:', value):
        return False, 'absolute path'
    if '..' in p.parts:
        return False, 'path escape'
    return True, str((root / p).resolve())


def check_task(root, task_dir):
    errors, warnings = [], []
    name = task_dir.name
    dpath = task_dir / 'delivery.json'
    if not dpath.exists():
        return {'task_id': name, 'ok': False, 'errors': ['delivery.json missing'], 'warnings': []}
    try:
        d = json.loads(dpath.read_text(encoding='utf-8-sig'))
    except Exception as exc:                                    # noqa: BLE001 - report, never raise
        return {'task_id': name, 'ok': False, 'errors': [f'delivery.json is not JSON: {exc}'], 'warnings': []}

    for key in REQUIRED_KEYS:
        if key not in d:
            errors.append(f'missing key: {key}')
    if d.get('task_id') != name:
        errors.append(f"task_id {d.get('task_id')!r} does not match directory {name!r}")
    if d.get('status') not in STATUSES:
        errors.append(f"status {d.get('status')!r} outside the vocabulary {sorted(STATUSES)}")
    for flag in ('lean_run', 'editor_run', 'native_iut_realized', 'fact_tree_admitted'):
        if d.get(flag) is not False:
            errors.append(f'{flag} must be false for a non-Lean static task, found {d.get(flag)!r}')

    # every declared path must exist inside the repo, and every declared hash must be recomputed
    for section in ('inputs', 'outputs'):
        entries = d.get(section)
        if not isinstance(entries, list) or not entries:
            errors.append(f'{section} is empty')
            continue
        for i, e in enumerate(entries):
            if not isinstance(e, dict) or 'path' not in e or 'sha256' not in e:
                errors.append(f'{section}[{i}] lacks path/sha256')
                continue
            ok, resolved = safe_rel(root, e['path'])
            if not ok:
                errors.append(f"{section}[{i}] path rejected: {resolved}")
                continue
            p = Path(resolved)
            if not p.exists():
                errors.append(f"{section}[{i}] missing on disk: {e['path']}")
                continue
            if not SHA_RE.match(str(e['sha256'])):
                errors.append(f"{section}[{i}] sha256 is not 64 lowercase hex: {e['sha256']!r}")
                continue
            actual = sha256(p)
            if actual != e['sha256']:
                errors.append(f"{section}[{i}] hash mismatch for {e['path']}: declared {e['sha256'][:12]}, actual {actual[:12]}")

    out_paths = {e.get('path') for e in d.get('outputs') or [] if isinstance(e, dict)}
    summary_declared = any(str(p).replace('\\', '/').split('/')[-1] == 'SUMMARY.md' for p in out_paths)
    if not summary_declared:
        errors.append('SUMMARY.md is not declared among outputs')
    elif not (task_dir / 'SUMMARY.md').exists():
        errors.append('SUMMARY.md is declared but absent')
    if not (d.get('review_anchors') or []):
        warnings.append('no review_anchors: the reviewer has no指定 anchor to spot-check')

    # forbidden claims, scanned in every string of the delivery
    blob = json.dumps(d, ensure_ascii=False)
    for pattern, why in FORBIDDEN_CLAIMS:
        if pattern.search(blob):
            errors.append(f'forbidden claim in delivery.json: {why}')

    # nothing may live outside the task directory
    try:
        inside = (task_dir.resolve().is_relative_to(root.resolve()))
    except AttributeError:                                        # Python < 3.9
        inside = str(task_dir.resolve()).startswith(str(root.resolve()))
    if not inside:
        errors.append(f'task directory is outside the repo root: {task_dir}')
    for f in task_dir.rglob('*'):
        if not f.is_file():
            continue
        try:
            f.resolve().relative_to(task_dir.resolve())
        except ValueError:
            errors.append(f'file escapes its task directory: {f.name}')
    return {'task_id': name, 'ok': not errors, 'errors': errors, 'warnings': warnings}


def check_package(root, package, only=None):
    tasks = []
    if not package.exists():
        return {'package': str(package), 'tasks': [], 'summary': {'error': 'package directory missing'}}
    for task_dir in sorted(p for p in package.iterdir() if p.is_dir()):
        if only and task_dir.name not in only:
            continue
        tasks.append(check_task(root, task_dir))
    return {
        'package': str(package),
        'tasks': tasks,
        'summary': {
            'tasks': len(tasks),
            'clean': sum(1 for t in tasks if t['ok']),
            'with_findings': sum(1 for t in tasks if not t['ok']),
            'not_a_math_check': True,
        },
    }


def selftest(report_holder):
    """Prove the checker rejects the four failure modes it exists for."""
    root = Path(__file__).resolve().parents[3]
    package = Path(__file__).resolve().parents[1]
    real = [p for p in package.iterdir() if p.is_dir() and (p / 'delivery.json').exists()]
    if not real:
        return ['selftest skipped: no delivery.json yet in the package']
    results = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for case in ('corrupt_hash', 'missing_summary', 'status_vocabulary', 'path_escape', 'editor_claim'):
            # the copied directory keeps the real task name, so a finding cannot be dismissed as an
            # artefact of renaming the task
            victim = tmp / case / real[0].name
            victim.mkdir(parents=True)
            for p in real[0].rglob('*'):
                if p.is_file():
                    dest = victim / p.relative_to(real[0])
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(p, dest)
            dpath = victim / 'delivery.json'
            d = json.loads(dpath.read_text(encoding='utf-8-sig'))
            if case == 'corrupt_hash':
                if d['outputs']:
                    d['outputs'][0]['sha256'] = '0' * 64
            elif case == 'missing_summary':
                (victim / 'SUMMARY.md').unlink(missing_ok=True)
                d['outputs'] = [o for o in d['outputs'] if o.get('path') != 'SUMMARY.md']
            elif case == 'status_vocabulary':
                d['status'] = 'DONE'
            elif case == 'path_escape':
                d['inputs'] = d.get('inputs') or [{'path': 'x', 'sha256': '0' * 64}]
                d['inputs'][0]['path'] = '../../etc/passwd'
            elif case == 'editor_claim':
                d['unresolved'] = list(d.get('unresolved') or []) + ['W11: EDITOR_CHECKED by the editor']
            dpath.write_text(json.dumps(d, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
            one = check_task(root, victim)
            caught = not one['ok']
            results.append(f'{case}: {"rejected" if caught else "NOT REJECTED"} '
                           + (f"({one['errors'][0][:80]})" if one['errors'] else ''))
    report_holder.append({'selftest': results})
    return results


def main(argv=None):
    ap = argparse.ArgumentParser(description='static checker for a non-Lean delivery package')
    ap.add_argument('--root', default='')
    ap.add_argument('--package', default='')
    ap.add_argument('--only', default='', help='comma-separated task ids')
    ap.add_argument('--json-out', default='')
    ap.add_argument('--selftest', action='store_true')
    args = ap.parse_args(argv)

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parents[3]
    package = Path(args.package).resolve() if args.package else Path(__file__).resolve().parents[1]
    only = {x.strip() for x in args.only.split(',') if x.strip()} or None

    holder = []
    report = check_package(root, package, only)
    if args.selftest:
        report['selftest'] = selftest(holder)
    text = json.dumps(report, ensure_ascii=False, indent=2) + '\n'
    if args.json_out:
        Path(args.json_out).write_text(text, encoding='utf-8')
    sys.stdout.write(text)
    bad = report['summary'].get('with_findings', 0)
    return 1 if bad else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:                                     # noqa: BLE001
        sys.stderr.write(f'checker failed to run: {exc}\n')
        sys.exit(2)
