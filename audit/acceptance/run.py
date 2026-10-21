"""P0: thin delivery-bundle checker and replay launcher (reviewer-freezable).

Purpose
-------
A task delivery is verified without trusting the deliverer. The launcher:

1. validates the bundle schema (explicit version, required fields, unknown fields rejected);
2. validates the exact base/head commits against the frozen contract, and the change set
   against the frozen allowed_paths (via the real git diff, not the bundle's claims);
3. validates that the bundle's *declared* check set exactly covers the frozen required
   case ids, and that each declared argv is the frozen allowlisted argv (nothing extra runs);
4. re-runs every allowlisted command itself, with a per-check timeout, capturing exit code
   and logs, and compares its own measurement with what the bundle claims;
5. verifies shipped log digests, and that a check claimed PASS really exited 0;
6. writes verdict.json and a one-page summary; exits 0 only when the verdict is PASS.

The launcher's own failure must never look like success: any unexpected exception is
reported as FAIL with a nonzero exit.

It does not review code semantics and does not grant mathematical admission. Expected values
come from the frozen contract/plan, never from the candidate bundle.
"""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

SCHEMA_VERSION = 1
REQUIRED_BUNDLE_FIELDS = (
    'schema', 'status', 'task_id', 'base_commit', 'head_commit',
    'scope_contract_sha256', 'source_tree_clean', 'environment', 'changes',
    'checks', 'mathematics', 'open_obligations', 'limitations', 'summary_path',
)
REQUIRED_MATHEMATICS_FIELDS = ('candidate_only', 'theorems')


def sha256_file(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load_json(path):
    # Accept a UTF-8 BOM: it is a transport artefact of some Windows writers, not a bundle
    # defect, and rejecting it would turn a valid delivery into a launcher exception.
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def git_blob_sha256(repo, spec):
    """SHA-256 of the raw blob bytes at ``spec`` (as a clean checkout would write it).

    Must not go through text mode: Python's universal-newline translation would hash
    ``\\r\\n`` as ``\\n`` and disagree with the delivered digest on a CRLF checkout.
    """
    result = subprocess.run(['git', '-C', str(repo), 'cat-file', 'blob', spec],
                            capture_output=True, timeout=120)
    if result.returncode != 0:
        return None
    return hashlib.sha256(result.stdout).hexdigest()


def git(repo, *args, timeout=120):
    result = subprocess.run(['git', '-C', str(repo), *args], capture_output=True,
                            text=True, encoding='utf-8', timeout=timeout)
    return result.returncode, result.stdout, result.stderr


class Verdict:
    def __init__(self, task_id):
        self.task_id = task_id
        self.failures = []
        self.incomplete = []
        self.notes = []
        self.checks = []
        self.scope = {'ok': False, 'violations': []}
        self.status = 'INCOMPLETE'

    def fail(self, code, detail):
        self.failures.append({'code': code, 'detail': detail})

    def note_incomplete(self, code, detail):
        """Timeout / missing artefact / manual step: report INCOMPLETE, never PASS or FAIL."""
        self.incomplete.append({'code': code, 'detail': detail})

    @property
    def passed(self):
        return not self.failures and all(c['status'] == 'PASS' for c in self.checks) \
            and self.scope['ok']


def allowed(path, patterns):
    return any(fnmatch.fnmatch(path, pat.replace('**', '*')) for pat in patterns)


def path_matches(path, patterns):
    """Strict segment-wise match so ``audit/acceptance/**`` cannot authorise ``audit/x``."""
    parts = path.split('/')
    for pat in patterns:
        want = pat.rstrip('/').split('/')
        if len(want) > len(parts):
            continue
        ok = True
        for index, segment in enumerate(want):
            if segment == '**':
                return True
            if not fnmatch.fnmatch(parts[index], segment):
                ok = False
                break
        if ok and len(want) == len(parts):
            return True
    return False


def validate_bundle(bundle, contract, plan, repo, verdict):
    missing = [f for f in REQUIRED_BUNDLE_FIELDS if f not in bundle]
    if missing:
        verdict.fail('P0.bundle_missing_fields', f'missing bundle fields: {missing}')
        return False
    unknown = sorted(set(bundle) - set(REQUIRED_BUNDLE_FIELDS)
                     - set(plan.get('allowed_bundle_extra_fields', [])))
    if unknown:
        verdict.fail('P0.bundle_unknown_fields', f'unknown bundle fields: {unknown}')
        return False
    extras = sorted(set(bundle) & set(plan.get('allowed_bundle_extra_fields', [])))
    if extras:
        verdict.notes.append({'code': 'P0.bundle_extra_fields',
                              'detail': f'tolerated non-executable fields: {extras}'})
    if bundle.get('schema') != SCHEMA_VERSION:
        verdict.fail('P0.bundle_schema', f'schema must be {SCHEMA_VERSION}, '
                                        f'got {bundle.get("schema")!r}')
        return False
    task = next((t for t in contract['tasks'] if t['id'] == bundle['task_id']), None)
    if task is None:
        verdict.fail('P0.unknown_task', f'unknown task id {bundle["task_id"]!r}')
        return False

    # Frozen expectations: base commit and the frozen contract digest. The expected base
    # comes from the frozen plan when it declares one (a reviewer may accept a task whose
    # base differs from the contract's default only by re-freezing the plan).
    frozen_base = plan.get('expected_base_commit') or contract['base_commit']
    if bundle['base_commit'] != frozen_base:
        verdict.fail('P0.changed_frozen_expectation',
                     f'base_commit {bundle["base_commit"]} != frozen {frozen_base}')
        return False
    contract_digest = plan.get('contract_sha256')
    if bundle['scope_contract_sha256'] != contract_digest:
        verdict.fail('P0.changed_frozen_expectation',
                     'scope_contract_sha256 does not match the frozen contract digest')
        return False

    # Real repository required; a bare archive cannot prove the source/result identity.
    rc, _, _ = git(repo, 'rev-parse', '--git-dir')
    if rc != 0:
        verdict.fail('P0.missing_git_context',
                     f'{repo} is not a git checkout; commit identity cannot be verified')
        return False
    rc, head_out, _ = git(repo, 'rev-parse', '--verify', '--quiet',
                          f'{bundle["head_commit"]}^{{commit}}')
    if rc != 0:
        verdict.fail('P0.wrong_commit', f'head_commit {bundle["head_commit"]} not in repository')
        return False
    head_sha = head_out.strip()
    rc, base_out, _ = git(repo, 'rev-parse', '--verify', '--quiet',
                          f'{bundle["base_commit"]}^{{commit}}')
    if rc != 0:
        verdict.fail('P0.wrong_commit', f'base_commit {bundle["base_commit"]} not in repository')
        return False
    rc, _, _ = git(repo, 'merge-base', '--is-ancestor', base_out.strip(), head_sha)
    if rc != 0:
        verdict.fail('P0.wrong_commit', 'head_commit is not a descendant of base_commit')
        return False

    if bundle['source_tree_clean'] is not None:
        # Commit identity is what matters: tracked modifications contradict a "clean" claim,
        # untracked scratch files do not (they cannot enter the commit, and the scope check
        # covers what did). Untracked entries are reported, not failed.
        rc, status, _ = git(repo, 'status', '--porcelain', '--untracked-files=no')
        dirty = status.strip()
        if bundle['source_tree_clean'] and rc == 0 and dirty:
            verdict.fail('P0.source_tree_dirty', f'claimed clean but tracked files changed: {dirty[:200]}')
            return False
        rc_all, all_status, _ = git(repo, 'status', '--porcelain')
        untracked = [line[3:] for line in all_status.splitlines() if line.startswith('??')]
        if untracked:
            verdict.notes.append({'code': 'P0.untracked_present',
                                  'detail': f'{len(untracked)} untracked path(s), e.g. '
                                            f'{untracked[:3]} — not part of the commit, not a '
                                            f'cleanliness defect'})

    rc, diff, _ = git(repo, 'diff', '--name-only', base_out.strip(), head_sha)
    changed = [line for line in diff.splitlines() if line.strip()]
    violations = [p for p in changed if not path_matches(p, task['allowed_paths'])]
    verdict.scope = {'ok': not violations, 'violations': violations, 'changed': changed}
    if violations:
        verdict.fail('P0.scope_violation',
                     f'paths outside allowed_paths for {task["id"]}: {violations}')
        return False

    declared = {c['path']: c for c in bundle['changes'] if 'path' in c}
    if sorted(declared) != sorted(changed):
        verdict.fail('P0.changes_mismatch',
                     f'declared changes {sorted(declared)} != git diff {sorted(changed)}')
        return False
    for path, row in declared.items():
        actual = git_blob_sha256(repo, f'{head_sha}:{path}')
        if actual is None:
            verdict.fail('P0.changes_mismatch', f'{path} not present at head_commit')
            return False
        if row.get('sha256') != actual:
            verdict.fail('P0.changes_mismatch',
                         f'{path}: declared sha256 {str(row.get("sha256"))[:16]} does not match '
                         f'the blob {actual[:16]}')
            return False
        if not str(row.get('purpose', '')).strip():
            verdict.fail('P0.changes_mismatch', f'{path}: purpose is empty')
            return False
    return True


def validate_check_declarations(bundle, task, plan, repo, verdict):
    required = list(task['required_case_ids'])
    frozen_plan = plan['cases']
    declared = {c.get('id'): c for c in bundle['checks'] if isinstance(c, dict)}
    missing = [cid for cid in required if cid not in declared]
    if missing:
        verdict.fail('P0.skipped_required_check', f'required cases not declared: {missing}')
    # Supplementary checks are not part of the verdict, but they must not smuggle in an
    # arbitrary command: the program/script prefix must be one the frozen plan already
    # authorises. Their logs are verified, nothing more.
    frozen_prefixes = {tuple(spec['argv'][:3]) for spec in frozen_plan.values()
                       if 'argv' in spec and len(spec['argv']) >= 3}
    # A task may also run the tool it is testing as supplementary evidence; that program is
    # declared per task in the frozen plan, never supplied by the bundle.
    for prefix in plan.get('supplementary_programs', {}).get(task['id'], []):
        frozen_prefixes.add(tuple(prefix))
    for cid in sorted(set(declared) - set(required)):
        entry = declared[cid]
        argv = list(entry.get('argv', []))
        if tuple(argv[:3]) not in frozen_prefixes:
            verdict.fail('P0.unapproved_command',
                         f'{cid}: supplementary check invokes an unauthorised program {argv[:3]}')
            continue
        problems = []
        for stream in ('stdout', 'stderr'):
            rel = entry.get(f'{stream}_path')
            digest = entry.get(f'{stream}_sha256')
            log_path = Path(entry.get('_base_dir', '.')) / rel if rel else None
            if not log_path or not log_path.exists():
                problems.append(f'missing {stream} log')
            elif digest and sha256_file(log_path) != digest:
                problems.append(f'{stream} digest mismatch')
        verdict.notes.append({'code': 'P0.supplementary_check',
                              'detail': f'{cid}: not required; '
                                        f'{"logs verified" if not problems else problems}'})
    for cid in required:
        if cid not in declared:
            continue
        entry = declared[cid]
        spec = frozen_plan.get(cid)
        if spec is None:
            verdict.fail('P0.unapproved_command', f'{cid} has no frozen allowlist entry')
            continue
        if spec.get('manual'):
            # Reviewer-only step: no argv, no logs, nothing to replay here.
            continue
        if list(entry.get('argv', [])) != list(spec['argv']):
            verdict.fail('P0.unapproved_command',
                         f'{cid}: argv {entry.get("argv")} != frozen {spec["argv"]}')
        # The allowlist fixes *which directory* a command runs in, not how the bundle spells
        # it: an absolute path is accepted only when it resolves to the frozen location.
        frozen_cwd = repo if spec.get('cwd', '.') in ('.', '') else (repo / spec['cwd'])
        claimed_cwd = Path(str(entry.get('cwd', '')))
        claimed_resolved = (claimed_cwd if claimed_cwd.is_absolute() else repo / claimed_cwd)
        try:
            same_dir = claimed_resolved.resolve() == frozen_cwd.resolve()
        except OSError:
            same_dir = False
        if not same_dir:
            verdict.fail('P0.unapproved_command',
                         f'{cid}: cwd {str(claimed_cwd)!r} does not resolve to the frozen '
                         f'{str(frozen_cwd)!r}')
        for stream in ('stdout', 'stderr'):
            rel = entry.get(f'{stream}_path')
            digest = entry.get(f'{stream}_sha256')
            if not rel or not digest:
                verdict.fail('P0.missing_log', f'{cid}: missing {stream} log path or digest')
                continue
            log_path = Path(entry.get('_base_dir', '.')) / rel
            if not log_path.exists():
                verdict.fail('P0.missing_log', f'{cid}: {log_path} does not exist')
                continue
            if sha256_file(log_path) != digest:
                verdict.fail('P0.log_digest_mismatch', f'{cid}: {stream} digest mismatch')
    return not verdict.failures


def execute(spec, repo, timeout):
    rel = spec.get('cwd', '.')
    cwd = repo if rel in ('.', '') else repo / rel
    started = time.time()
    try:
        result = subprocess.run(spec['argv'], cwd=str(cwd), capture_output=True, text=True,
                                encoding='utf-8', errors='replace', timeout=timeout)
        return {'exit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr,
                'elapsed': round(time.time() - started, 3), 'timed_out': False}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'stdout': '', 'stderr': '', 'elapsed': timeout, 'timed_out': True}
    except OSError as exc:
        return {'exit': None, 'stdout': '', 'stderr': str(exc), 'elapsed': round(time.time() - started, 3),
                'timed_out': False}


def replay(bundle, task, plan, repo, verdict, timeout_override=None):
    declared = {c.get('id'): c for c in bundle['checks'] if isinstance(c, dict)}
    for cid in task['required_case_ids']:
        spec = plan['cases'].get(cid)
        entry = declared.get(cid, {})
        if spec is None or cid not in declared:
            verdict.checks.append({'id': cid, 'status': 'SKIPPED'})
            continue
        if spec.get('manual'):
            # Reviewer-only step (e.g. actual VS Code replay). The launcher must never
            # report PASS for it; it reports that a manual step is outstanding.
            verdict.checks.append({'id': cid, 'status': 'MANUAL_REQUIRED',
                                   'detail': spec.get('note', 'reviewer must perform this step')})
            continue
        timeout = timeout_override or spec.get('timeout_seconds', 300)
        measured = execute(spec, repo, timeout)
        claimed_exit = entry.get('exit_code')
        claimed_outcome = entry.get('outcome')
        expected_exit = spec.get('expected_exit', 0)
        status = 'PASS'
        if measured['timed_out']:
            status = 'INCOMPLETE'
            verdict.note_incomplete('P0.timeout', f'{cid}: exceeded {timeout}s')
        elif measured['exit'] is None:
            status = 'INCOMPLETE'
            verdict.note_incomplete('P0.execution_error',
                                    f'{cid}: could not run ({measured["stderr"][:120]})')
        else:
            if claimed_outcome == 'PASS' and (claimed_exit != expected_exit
                                              or measured['exit'] != expected_exit):
                status = 'FAIL'
                verdict.fail('P0.failed_check_claimed_pass',
                             f'{cid}: claimed PASS but exits claimed={claimed_exit} '
                             f'measured={measured["exit"]} expected={expected_exit}')
            elif measured['exit'] != claimed_exit and claimed_exit is not None:
                status = 'FAIL'
                verdict.fail('P0.replay_mismatch',
                             f'{cid}: bundle claims exit {claimed_exit}, replay measured '
                             f'{measured["exit"]}')
            elif claimed_outcome not in ('PASS', 'FAIL', 'INCOMPLETE'):
                status = 'FAIL'
                verdict.fail('P0.bad_outcome', f'{cid}: outcome {claimed_outcome!r}')
        verdict.checks.append({'id': cid, 'status': status,
                               'measured_exit': measured['exit'],
                               'claimed_exit': claimed_exit,
                               'claimed_outcome': claimed_outcome,
                               'elapsed_seconds': measured['elapsed'],
                               'replay_stdout_head': measured['stdout'][:400],
                               'replay_stderr_head': measured['stderr'][:400]})


def summarise(verdict, out_path, task_id, base, head):
    passed = [c for c in verdict.checks if c['status'] == 'PASS']
    incomplete = [c for c in verdict.checks if c['status'] == 'INCOMPLETE']
    failed = [c for c in verdict.checks if c['status'] == 'FAIL']
    moved = verdict.scope.get('changed', [])
    lines = [
        f'P0 acceptance replay — task {task_id}',
        f'base {base}  head {head}',
        f'verdict: {verdict.status}',
        f'checks: {len(verdict.checks)} total / {len(passed)} pass / {len(failed)} fail / '
        f'{len(incomplete)} incomplete',
        f'scope: {"ok" if verdict.scope["ok"] else "VIOLATION"}, {len(moved)} changed path(s)',
        f'failures: {len(verdict.failures)}',
    ]
    for item in verdict.failures[:12]:
        lines.append(f'  - {item["code"]}: {item["detail"][:160]}')
    for item in verdict.incomplete[:12]:
        lines.append(f'  ~ {item["code"]}: {item["detail"][:160]}')
    lines.append('mathematical admission: none (P0 never grants it); reviewer VS Code replay '
                 'still required for math tasks')
    text = '\n'.join(lines)
    Path(out_path).write_text(text + '\n', encoding='utf-8')
    return text


def main(argv=None):
    parser = argparse.ArgumentParser(description='Thin bundle checker and replay launcher (P0).')
    parser.add_argument('--bundle', required=False, help='path to the delivery bundle.json')
    parser.add_argument('--task', help='task id (must match the bundle when given)')
    parser.add_argument('--repo', default='.', help='git checkout to verify against')
    parser.add_argument('--contract', default='handoffs/next-round/contracts.json')
    parser.add_argument('--plan', default='audit/acceptance/plan.json')
    parser.add_argument('--out', help='verdict/summary path (default: beside the bundle)')
    parser.add_argument('--timeout', type=float, help='override every per-check timeout')
    args = parser.parse_args(argv)

    task_id = args.task or 'UNKNOWN'
    base = head = 'UNKNOWN'
    out_dir = Path(args.bundle).resolve().parent if args.bundle else Path.cwd()
    verdict = Verdict(task_id)
    try:
        if not args.bundle:
            verdict.fail('P0.no_bundle', '--bundle is required')
            raise SystemExit(2)
        repo = Path(args.repo).resolve()
        plan = load_json(args.plan)
        contract_path = Path(args.contract)
        contract = load_json(contract_path)
        frozen_digest = hashlib.sha256(contract_path.read_bytes()).hexdigest()
        if plan.get('contract_sha256') != frozen_digest:
            verdict.fail('P0.plan_contract_mismatch',
                         'plan.json was not frozen against this contracts.json digest')
        bundle = load_json(args.bundle)
        task_id = bundle.get('task_id', 'UNKNOWN')
        verdict.task_id = task_id
        base = bundle.get('base_commit', 'UNKNOWN')
        head = bundle.get('head_commit', 'UNKNOWN')
        bundle_dir = Path(args.bundle).resolve().parent
        for entry in bundle.get('checks', []):
            if isinstance(entry, dict):
                entry['_base_dir'] = str(bundle_dir)
        if args.task and args.task != task_id:
            verdict.fail('P0.task_mismatch', f'--task {args.task} != bundle {task_id}')
        if validate_bundle(bundle, contract, plan, repo, verdict):
            if validate_check_declarations(bundle, next(t for t in contract['tasks']
                                                         if t['id'] == task_id),
                                           plan, repo, verdict):
                replay(bundle, next(t for t in contract['tasks'] if t['id'] == task_id),
                       plan, repo, verdict, args.timeout)
        verdict.status = ('PASS' if verdict.passed
                          else ('FAIL' if verdict.failures else 'INCOMPLETE'))
    except SystemExit:
        raise
    except Exception as exc:  # launcher trouble must never look like success
        verdict.fail('P0.launcher_exception', f'{type(exc).__name__}: {exc}')
        verdict.status = 'FAIL'

    out_path = Path(args.out) if args.out else out_dir / 'verdict.json'
    payload = {'schema': SCHEMA_VERSION, 'task_id': task_id, 'base_commit': base,
               'head_commit': head, 'status': verdict.status,
               'checks': verdict.checks, 'failures': verdict.failures,
               'incomplete': verdict.incomplete,
               'notes': verdict.notes,
               'scope': verdict.scope,
               'mathematical_admission': False,
               'note': ('PASS means the bundle metadata, scope and replay agree with the frozen '
                        'contract. It is not code review and not mathematical admission.')}
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    summary = summarise(verdict, out_path.parent / 'summary.txt', task_id, base, head)
    print(summary)
    print(f'verdict written: {out_path}')
    return 0 if verdict.status == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
