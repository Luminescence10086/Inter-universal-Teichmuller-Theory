"""Frozen negative/positive cases for the P0 launcher.

Usage:
  python -B audit/acceptance/tests/test_run.py               # all cases
  python -B audit/acceptance/tests/test_run.py P0.valid_bundle

Each required case builds its own throw-away git checkout and bundle under a temporary
directory, runs the real launcher in-process, and asserts the verdict. Exit code 0 means
every executed case behaved as the frozen contract requires; a missing argument runs all.
"""
from __future__ import annotations

import hashlib
import io
import json
import subprocess
import sys
import tempfile
import time
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'audit/acceptance'))
import run as launcher  # noqa: E402

CONTRACT = ROOT / 'handoffs/next-round/contracts.json'
PLAN = ROOT / 'audit/acceptance/plan.json'
CONTRACT_DIGEST = hashlib.sha256(CONTRACT.read_bytes()).hexdigest()
REQUIRED = json.loads(CONTRACT.read_text(encoding='utf-8'))
P0_IDS = next(t for t in REQUIRED['tasks'] if t['id'] == 'P0')['required_case_ids']

PROBE_OK = """import sys, time
mode = sys.argv[1] if len(sys.argv) > 1 else 'ok'
if mode == 'slow':
    time.sleep(5)
print('probe', mode)
raise SystemExit(0)
"""

PROBE_FAIL = """import sys
print('probe deliberately failing')
raise SystemExit(1)
"""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], capture_output=True,
                          text=True, encoding='utf-8')


def make_repo(tmp: Path, probe_source: str = PROBE_OK, with_git: bool = True):
    repo = tmp / 'repo'
    (repo / 'audit/acceptance').mkdir(parents=True)
    (repo / 'audit/acceptance/probe.py').write_text(probe_source, encoding='utf-8')
    (repo / 'audit/acceptance/impl.txt').write_text('baseline\n', encoding='utf-8')
    if not with_git:
        return repo, None, None
    git(repo, 'init', '-q')
    git(repo, 'config', 'user.email', 'fixture@example.invalid')
    git(repo, 'config', 'user.name', 'fixture')
    git(repo, 'add', '-A')
    git(repo, 'commit', '-q', '-m', 'baseline')
    base = git(repo, 'rev-parse', 'HEAD').stdout.strip()
    (repo / 'audit/acceptance/impl.txt').write_text('baseline\nimplementation\n', encoding='utf-8')
    git(repo, 'add', '-A')
    git(repo, 'commit', '-q', '-m', 'implementation')
    head = git(repo, 'rev-parse', 'HEAD').stdout.strip()
    return repo, base, head


def make_bundle(tmp: Path, repo, base, head, *, drop_case=None, bad_digest=False,
                extra_command=False, wrong_scope=False, outcome='PASS', exit_code=0):
    bundle_dir = tmp / 'bundle'
    (bundle_dir / 'logs').mkdir(parents=True, exist_ok=True)
    if head is None:
        head = '0' * 40
        base = '1' * 40
    blob = git(repo, 'show', f'{head}:audit/acceptance/impl.txt').stdout if repo else ''
    changes = [{'path': 'audit/acceptance/impl.txt',
                'sha256': sha256_bytes(blob.encode('utf-8')),
                'purpose': 'fixture implementation change'}]
    checks = []
    for cid in P0_IDS:
        if cid == drop_case:
            continue
        argv = ['python', '-B', 'audit/acceptance/probe.py',
                'slow' if cid == 'P0.timeout' else 'ok']
        if extra_command and cid == 'P0.valid_bundle':
            argv = argv + ['--extra-unapproved-argument']
        out_rel = f'logs/{cid}.stdout.txt'
        err_rel = f'logs/{cid}.stderr.txt'
        (bundle_dir / out_rel).write_text('probe ok\n', encoding='utf-8')
        (bundle_dir / err_rel).write_text('', encoding='utf-8')
        checks.append({
            'id': cid, 'argv': argv, 'cwd': '.', 'exit_code': exit_code,
            'elapsed_seconds': 0.1, 'stdout_path': out_rel,
            'stdout_sha256': sha256_bytes((bundle_dir / out_rel).read_bytes()),
            'stderr_path': err_rel,
            'stderr_sha256': sha256_bytes((bundle_dir / err_rel).read_bytes()),
            'outcome': outcome})
    if bad_digest and checks:
        checks[0]['stdout_sha256'] = '0' * 64
    bundle = {
        'schema': 1, 'status': 'RESULT', 'task_id': 'P0',
        'base_commit': base, 'head_commit': head,
        'scope_contract_sha256': 'f' * 64 if wrong_scope else CONTRACT_DIGEST,
        'source_tree_clean': True,
        'environment': {'os': sys.platform, 'python': sys.version.split()[0],
                        'lean': None, 'lake': None, 'dependency_locks': []},
        'changes': changes, 'checks': checks,
        'mathematics': {'candidate_only': True, 'theorems': [],
                        'cli_zero_diagnostics': None, 'vscode_observation': None,
                        'reviewer_vscode_replay_complete': False, 'new_formal_admissions': 0},
        'open_obligations': [], 'limitations': [], 'summary_path': 'SUMMARY.md'}
    (bundle_dir / 'bundle.json').write_text(json.dumps(bundle, indent=2), encoding='utf-8')
    (bundle_dir / 'SUMMARY.md').write_text('fixture\n', encoding='utf-8')
    return bundle_dir / 'bundle.json'


def fixture_plan(tmp: Path, base: str) -> Path:
    """Frozen plan re-frozen against the fixture's own base commit.

    The launcher must take expected values from the frozen plan, never from the bundle, so
    a fixture re-freezes the plan with ``expected_base_commit`` instead of pretending its
    throw-away repository has the real contract base.
    """
    plan = json.loads(PLAN.read_text(encoding='utf-8'))
    plan['expected_base_commit'] = base
    path = tmp / 'plan.fixture.json'
    path.write_text(json.dumps(plan, ensure_ascii=False, indent=2), encoding='utf-8')
    return path


def invoke(bundle_path, repo, *, timeout=None, plan=None):
    args = ['--bundle', str(bundle_path), '--repo', str(repo),
            '--contract', str(CONTRACT), '--plan', str(plan or PLAN)]
    if timeout is not None:
        args += ['--timeout', str(timeout)]
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        code = launcher.main(args)
    verdict_path = Path(bundle_path).parent / 'verdict.json'
    verdict = json.loads(verdict_path.read_text(encoding='utf-8')) if verdict_path.exists() else {}
    return code, verdict, buffer.getvalue()


def codes(verdict):
    return ([f['code'] for f in verdict.get('failures', [])]
            + [f['code'] for f in verdict.get('incomplete', [])])


CASES = {}


def case(name):
    def register(fn):
        CASES[name] = fn
        return fn
    return register


@case('P0.valid_bundle')
def _valid(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code == 0, f'valid bundle must PASS, got code {code}: {codes(verdict)}'
    assert verdict['status'] == 'PASS', verdict['status']
    assert verdict['mathematical_admission'] is False
    assert len(verdict['checks']) == len(P0_IDS)
    assert sum(not check['deduplicated'] for check in verdict['checks']) == 2
    assert any(check['deduplicated'] for check in verdict['checks'])


@case('P0.wrong_commit')
def _wrong_commit(tmp):
    repo, base, _ = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, 'f' * 40)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.wrong_commit' in codes(verdict), codes(verdict)


@case('P0.missing_log')
def _missing_log(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head)
    data = json.loads(bundle.read_text(encoding='utf-8'))
    (Path(bundle).parent / data['checks'][0]['stdout_path']).unlink()
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.missing_log' in codes(verdict), codes(verdict)


@case('P0.log_digest_mismatch')
def _digest_mismatch(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head, bad_digest=True)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.log_digest_mismatch' in codes(verdict), codes(verdict)


@case('P0.failed_check_claimed_pass')
def _claimed_pass(tmp):
    repo, base, head = make_repo(tmp, probe_source=PROBE_FAIL)
    bundle = make_bundle(tmp, repo, base, head)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.expected_exit_mismatch' in codes(verdict), codes(verdict)


@case('P0.failed_required_check_claimed_fail')
def _claimed_fail(tmp):
    repo, base, head = make_repo(tmp, probe_source=PROBE_FAIL)
    bundle = make_bundle(tmp, repo, base, head, outcome='FAIL', exit_code=1)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS', verdict
    assert 'P0.expected_exit_mismatch' in codes(verdict), codes(verdict)


@case('P0.author_incomplete')
def _author_incomplete(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head, outcome='INCOMPLETE', exit_code=0)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] == 'INCOMPLETE', verdict


@case('P0.checked_out_head_mismatch')
def _checked_out_head_mismatch(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head)
    data = json.loads(bundle.read_text(encoding='utf-8'))
    data['source_tree_clean'] = None
    bundle.write_text(json.dumps(data, indent=2), encoding='utf-8')
    git(repo, 'checkout', '-q', '--detach', base)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS', verdict
    assert 'P0.checked_out_head_mismatch' in codes(verdict), codes(verdict)


@case('P0.timeout')
def _timeout(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head)
    code, verdict, _ = invoke(bundle, repo, timeout=0.5, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert verdict['status'] == 'INCOMPLETE', verdict['status']
    assert 'P0.timeout' in codes(verdict), codes(verdict)


@case('P0.skipped_required_check')
def _skipped(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head, drop_case='P0.valid_bundle')
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.skipped_required_check' in codes(verdict), codes(verdict)


@case('P0.missing_git_context')
def _no_git(tmp):
    repo, _, _ = make_repo(tmp, with_git=False)
    base = '1' * 40
    bundle = make_bundle(tmp, repo, base, '2' * 40)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.missing_git_context' in codes(verdict), codes(verdict)


@case('P0.changed_frozen_expectation')
def _frozen(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head, wrong_scope=True)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.changed_frozen_expectation' in codes(verdict), codes(verdict)


@case('P0.unapproved_command')
def _unapproved(tmp):
    repo, base, head = make_repo(tmp)
    bundle = make_bundle(tmp, repo, base, head, extra_command=True)
    code, verdict, _ = invoke(bundle, repo, plan=fixture_plan(tmp, base))
    assert code != 0 and verdict['status'] != 'PASS'
    assert 'P0.unapproved_command' in codes(verdict), codes(verdict)


def main(argv):
    selected = argv or list(CASES)
    failures = []
    started = time.time()
    for name in selected:
        if name not in CASES:
            print(f'UNKNOWN {name}')
            failures.append(name)
            continue
        with tempfile.TemporaryDirectory() as tmpdir:
            try:
                CASES[name](Path(tmpdir))
                print(f'PASS {name}')
            except AssertionError as exc:
                print(f'FAIL {name}: {exc}')
                failures.append(name)
            except Exception as exc:  # noqa: BLE001 - a case that crashes is a failure
                print(f'ERROR {name}: {type(exc).__name__}: {exc}')
                failures.append(name)
    elapsed = time.time() - started
    print(f'{len(selected) - len(failures)}/{len(selected)} cases ok in {elapsed:.1f}s')
    return 0 if not failures else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
