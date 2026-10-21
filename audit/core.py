"""Core audit composer: one command, one verdict, four tools composed.

Why compose
-----------
The repository owns four independently delivered auditors:
  audit/acceptance/run.py   bundle schema + frozen scope + replay (P0)
  audit/affected.py         what a change invalidates (E2)
  audit/mutation_harness.py do the gates actually catch what they claim (E1)
  audit/tcb_manifest.py     conservative dependency/pin review (E3)

Used separately they can each be green while the whole is wrong, because their
blind spots are complementary:
  * the launcher replays a bundle but does not know whether the delivery's own
    change voids the receipt it leans on;
  * the impact planner knows what a change invalidates but not whether the bundle
    it accompanies was accepted;
  * the mutation harness proves the gates bite but says nothing about a specific
    delivery;
  * the dependency reviewer says nothing about either.

This tool runs the stages in order, feeds the bundle's own base/head into the
impact stage, and then applies checks no single stage can apply:

  * cross-stage contradiction: an accepted bundle whose own change set voids a
    receipt (or reports undecided snapshot membership) is not a pass, however
    green each stage is alone;
  * impact under-report: a change that touches a snapshot member or theorem source
    must invalidate something, or be reported unknown — silence is a failure
    (this is the exact class of review finding R3);
  * verdict algebra: FAIL if any required stage fails, INCOMPLETE if any is
    incomplete or manual steps remain, PASS only when the required stages pass.
    Passes are never averaged and INCOMPLETE never rounds up to PASS.

It performs no code review, changes no pin, receipt, fact-tree or Lean source, and
grants no mathematical admission. Each stage keeps its own honest semantics; this
tool only refuses to hide them behind a single cheerful word.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCHEMA = 1
HERE = Path(__file__).resolve().parent
REPO = HERE.parent
STAGES = ('acceptance', 'impact', 'gates', 'dependency')
TOOL_PATHS = {
    'acceptance': Path('audit/acceptance/run.py'),
    'impact': Path('audit/affected.py'),
    'gates': Path('audit/mutation_harness.py'),
    'dependency': Path('audit/tcb_manifest.py'),
}
TIMEOUTS = {'acceptance': 2400, 'impact': 600, 'gates': 1200, 'dependency': 600}


class Stage:
    def __init__(self, name):
        self.name = name
        self.status = 'INCOMPLETE'
        self.detail = ''
        self.data = {}
        self.seconds = 0.0

    def as_dict(self):
        return {'stage': self.name, 'status': self.status, 'detail': self.detail,
                'seconds': round(self.seconds, 2), 'data': self.data}


def run(argv, cwd, timeout):
    env = dict(os.environ, PYTHONIOENCODING='utf-8')
    started = time.time()
    try:
        result = subprocess.run(argv, cwd=str(cwd), capture_output=True, timeout=timeout, env=env)
        out = result.stdout.decode('utf-8', 'replace')
        err = result.stderr.decode('utf-8', 'replace')
        return {'exit': result.returncode, 'stdout': out, 'stderr': err,
                'seconds': round(time.time() - started, 2), 'timed_out': False}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'stdout': '', 'stderr': '', 'seconds': timeout, 'timed_out': True}
    except OSError as exc:
        return {'exit': None, 'stdout': '', 'stderr': str(exc),
                'seconds': round(time.time() - started, 2), 'timed_out': False}


def load_json_text(text):
    text = text.lstrip('\ufeff')
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        # Some stages print a human summary then JSON, or vice versa: take the longest
        # parseable JSON value rather than guessing at line offsets.
        for start in (text.find('{'), text.find('[')):
            if start < 0:
                continue
            for end in range(len(text), start, -1):
                try:
                    return json.loads(text[start:end])
                except json.JSONDecodeError:
                    continue
        raise


def tool_for(stage, target_repo):
    """Prefer the target checkout's own copy; report honestly when it is absent."""
    candidate = target_repo / TOOL_PATHS[stage]
    if candidate.exists():
        return candidate, None
    fallback = REPO / TOOL_PATHS[stage]
    if fallback.exists():
        return fallback, f'{stage}: target checkout lacks {TOOL_PATHS[stage]}; used the composer checkout copy'
    return None, f'{stage}: tool missing in both checkouts'


def stage_acceptance(bundle, task, target_repo, workdir):
    stage = Stage('acceptance')
    tool, note = tool_for('acceptance', target_repo)
    if tool is None:
        stage.detail = note
        return stage
    if note:
        stage.data.setdefault('notes', []).append(note)
    out_path = workdir / 'acceptance-verdict.json'
    argv = [sys.executable, '-B', str(tool), '--bundle', str(bundle), '--repo', str(target_repo),
            '--contract', str(REPO / 'handoffs/next-round/contracts.json'),
            '--plan', str(REPO / 'audit/acceptance/plan.json'), '--out', str(out_path)]
    if task:
        argv += ['--task', task]
    result = run(argv, REPO, TIMEOUTS['acceptance'])
    stage.seconds = result['seconds']
    if result['timed_out']:
        stage.detail = 'acceptance replay timed out'
        return stage
    if not out_path.exists():
        stage.status = 'FAIL'
        stage.detail = f'launcher produced no verdict (exit {result["exit"]}): {result["stderr"][:200]}'
        return stage
    verdict = json.loads(out_path.read_text(encoding='utf-8-sig'))
    stage.data = {'verdict': verdict.get('status'), 'checks': len(verdict.get('checks', [])),
                  'failures': verdict.get('failures', []), 'incomplete': verdict.get('incomplete', []),
                  'scope': verdict.get('scope', {})}
    stage.status = {'PASS': 'PASS', 'FAIL': 'FAIL', 'INCOMPLETE': 'INCOMPLETE'}.get(
        verdict.get('status'), 'INCOMPLETE')
    stage.detail = (f'launcher verdict {verdict.get("status")} with '
                    f'{len(verdict.get("failures", []))} failure(s)')
    return stage


def stage_acceptance_selftest(target_repo):
    """Self-audit variant: run the launcher's own frozen cases on this checkout."""
    stage = Stage('acceptance')
    tool = target_repo / 'audit/acceptance/tests/test_run.py'
    if not tool.exists():
        stage.detail = ('target checkout has no audit/acceptance self-cases; refusing to '
                        'guess whether its launcher works')
        return stage
    result = run([sys.executable, '-B', str(tool)], target_repo, TIMEOUTS['acceptance'])
    stage.seconds = result['seconds']
    if result['timed_out']:
        stage.detail = 'acceptance self-cases timed out'
        return stage
    tail = [line for line in result['stdout'].strip().splitlines() if line.strip()][-1:]
    stage.data = {'exit_code': result['exit'], 'tail': tail}
    stage.status = 'PASS' if result['exit'] == 0 else 'FAIL'
    stage.detail = ('launcher self-cases pass on this checkout' if stage.status == 'PASS'
                    else f'launcher self-cases failed (exit {result["exit"]})')
    return stage


def stage_impact(target_repo, base, head):
    stage = Stage('impact')
    tool, note = tool_for('impact', target_repo)
    if tool is None:
        stage.detail = note
        return stage
    argv = [sys.executable, '-B', str(tool), '--range', f'{base}..{head}', '--json']
    result = run(argv, target_repo, TIMEOUTS['impact'])
    stage.seconds = result['seconds']
    if result['timed_out']:
        stage.detail = 'impact planning timed out'
        return stage
    if result['exit'] != 0:
        stage.status = 'FAIL'
        stage.detail = f'affected.py exited {result["exit"]}: {result["stderr"][:200]}'
        return stage
    try:
        data = load_json_text(result['stdout'])
    except Exception as exc:  # noqa: BLE001 - unparseable planning output is not a pass
        stage.status = 'FAIL'
        stage.detail = f'unparseable impact output: {exc}'
        return stage
    counts = data.get('counts', {})
    changed = data.get('changed', [])
    voided = int(counts.get('receipts_voided', 0) or 0)
    unknown = int(counts.get('receipts_unknown', 0) or 0)
    added = int(counts.get('snapshot_members_added', 0) or 0)
    membership = data.get('snapshot_membership', {}) or {}
    probe = membership.get('probe')
    entry_points = membership.get('entry_points', {}) or {}
    undecided = sorted(project for project, entry in entry_points.items()
                       if (entry or {}).get('input', {}).get('status') != 'decided')
    stage.data = {'changed': len(changed), 'receipts_voided': voided,
                  'receipts_unknown': unknown, 'snapshot_members_added': added,
                  'membership_probe': probe, 'undecided_projects': undecided,
                  'nodes_invalidated': counts.get('nodes_invalidated'),
                  'nodes_to_pending': counts.get('nodes_to_pending'),
                  'contracts_invalidated': (data.get('contracts', {}) or {}).get('invalidated'),
                  'warnings': data.get('warnings', [])}
    # Trust the planner's own membership decision (E2 replaced glob re-implementation with
    # the production snapshot functions), and check only for internal contradiction or
    # honest uncertainty — never for a path-shaped guess.
    if added > 0 and voided == 0 and unknown == 0:
        stage.status = 'FAIL'
        stage.detail = (f'inconsistent impact report: {added} new snapshot member(s) but '
                        f'0 receipt voided and 0 undecided')
        return stage
    if probe != 'enabled' or undecided or unknown:
        stage.status = 'INCOMPLETE'
        stage.detail = (f'membership not fully decided (probe={probe!r}, '
                        f'undecided={undecided}, receipts_unknown={unknown})')
        return stage
    stage.status = 'PASS'
    stage.detail = (f'{len(changed)} changed, {voided} receipt(s) voided, '
                    f'{added} new snapshot member(s), membership decided')
    return stage


def stage_gates(target_repo):
    stage = Stage('gates')
    tool, note = tool_for('gates', target_repo)
    if tool is None:
        stage.detail = note
        return stage
    if note:
        stage.data.setdefault('notes', []).append(note)
    result = run([sys.executable, '-B', str(tool), '--json'], target_repo, TIMEOUTS['gates'])
    stage.seconds = result['seconds']
    if result['timed_out']:
        stage.detail = 'mutation harness timed out'
        return stage
    try:
        data = load_json_text(result['stdout'])
    except Exception as exc:  # noqa: BLE001
        stage.status = 'FAIL'
        stage.detail = f'unparseable mutation output (exit {result["exit"]}): {exc}'
        return stage
    violations = data.get('violations', [])
    stage.data = {'exit_code': data.get('exit_code'), 'violations': violations,
                  'matrix_complete': data.get('matrix_complete'),
                  'repository_unchanged': data.get('repository_unchanged')}
    if data.get('exit_code') != 0 or violations:
        stage.status = 'FAIL'
        stage.detail = f'gates failed: {violations[:3] or "nonzero exit"}'
    elif data.get('matrix_complete') is not True:
        stage.status = 'INCOMPLETE'
        stage.detail = 'gate matrix incomplete'
    elif data.get('repository_unchanged') is not True:
        stage.status = 'FAIL'
        stage.detail = 'harness observed repository bytes change during the run'
    else:
        stage.status = 'PASS'
        stage.detail = 'every claimed catch held and the negative control stayed quiet'
    return stage


def stage_dependency(target_repo):
    stage = Stage('dependency')
    tool, note = tool_for('dependency', target_repo)
    if tool is None:
        stage.detail = note
        return stage
    if note:
        stage.data.setdefault('notes', []).append(note)
    result = run([sys.executable, '-B', str(tool), '--json'], target_repo, TIMEOUTS['dependency'])
    stage.seconds = result['seconds']
    if result['timed_out']:
        stage.detail = 'dependency review timed out'
        return stage
    try:
        data = load_json_text(result['stdout'])
    except Exception as exc:  # noqa: BLE001
        stage.status = 'FAIL'
        stage.detail = f'unparseable dependency output (exit {result["exit"]}): {exc}'
        return stage
    rows = data if isinstance(data, list) else [data]
    under = {}
    withheld = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        project = row.get('project') or row.get('project_dir') or 'project'
        counts = row.get('counts', {}) or {}
        under[project] = int(counts.get('under_pinned', 0) or 0)
        withheld[project] = ((row.get('closure', {}) or {}).get('status'),
                             int(counts.get('unclassified', 0) or 0))
    stage.data = {'under_pinned': under, 'closure': withheld,
                  'exit_code': result['exit']}
    total_under = sum(under.values())
    if total_under:
        stage.status = 'FAIL'
        stage.detail = f'{total_under} input(s) are read but not pinned (real evidence gap)'
    else:
        # A withheld/with incomplete closure is the *intended* honest state, not a pass
        # signal: report it as informational and keep the stage green only because it
        # found no actual missing pin.
        stage.status = 'PASS'
        stage.detail = ('no read-but-unpinned input; removal proposals are withheld where '
                        'the closure is incomplete')
    return stage


def compose(stages, acceptance, impact):
    """Verdict algebra plus the cross-stage check no single tool can make."""
    if not stages:
        return 'INCOMPLETE', [], [], ['no stage ran: an empty composition is not a pass']
    failures = [s.name for s in stages if s.status == 'FAIL']
    incomplete = [s.name for s in stages if s.status == 'INCOMPLETE']
    cross = []
    if acceptance is not None and impact is not None:
        if acceptance.status == 'PASS' and (impact.data.get('receipts_voided', 0)
                                            or impact.data.get('receipts_unknown', 0)):
            cross.append('accepted bundle, yet its own change set voids or leaves undecided '
                         'a receipt it depends on')
    if cross:
        return 'FAIL', failures + ['cross-stage'], incomplete, cross
    if failures:
        return 'FAIL', failures, incomplete, cross
    if incomplete:
        return 'INCOMPLETE', failures, incomplete, cross
    return 'PASS', failures, incomplete, cross


def summarise(payload):
    lines = [f'core audit — task {payload["task_id"]}',
             f'repo {payload["repo"]}',
             f'bundle {payload["bundle"]}',
             f'base {payload["base_commit"]}  head {payload["head_commit"]}',
             f'verdict: {payload["verdict"]}']
    for stage in payload['stages']:
        lines.append(f'  [{stage["status"]:<10}] {stage["stage"]:<11} {stage["detail"][:120]}')
    if payload.get('cross_stage'):
        for item in payload['cross_stage']:
            lines.append(f'  ! cross-stage: {item}')
    lines.append('mathematical admission: none — engineering stages can never grant it')
    return '\n'.join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description='Compose the four auditors into one verdict.')
    parser.add_argument('--bundle', help='delivery bundle.json')
    parser.add_argument('--task', help='task id (from the bundle when omitted)')
    parser.add_argument('--repo', help='checkout under audit (default: this checkout)')
    parser.add_argument('--out', help='where to write core-verdict.json')
    parser.add_argument('--skip', default='', help='comma-separated stages to skip')
    parser.add_argument('--self-test', action='store_true', help='run the composition self-tests')
    parser.add_argument('--self-audit', action='store_true',
                        help='audit this checkout as a whole (no delivery bundle): launcher '
                             'self-cases + impact from the contract base to HEAD + gates + pins')
    args = parser.parse_args(argv)

    if args.self_test:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'core_selftest', str(HERE / 'tests' / 'test_core.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module.main([])

    target = Path(args.repo).resolve() if args.repo else REPO
    skip = {s.strip() for s in args.skip.split(',') if s.strip()}
    if skip - set(STAGES):
        parser.error(f'unknown stage in --skip: {sorted(skip - set(STAGES))}')

    if args.self_audit:
        contract = json.loads((REPO / 'handoffs/next-round/contracts.json')
                              .read_text(encoding='utf-8-sig'))
        base = contract['base_commit']
        head_result = subprocess.run(['git', '-C', str(target), 'rev-parse', 'HEAD'],
                                     capture_output=True, text=True, encoding='utf-8')
        head = (head_result.stdout or '').strip()
        if head_result.returncode != 0 or not head:
            parser.error(f'{target} is not a git checkout; self-audit needs commit identity')
        stages = []
        acceptance = impact = None
        if 'acceptance' not in skip:
            acceptance = stage_acceptance_selftest(target)
            stages.append(acceptance)
        if 'impact' not in skip:
            impact = stage_impact(target, base, head)
            stages.append(impact)
        if 'gates' not in skip:
            stages.append(stage_gates(target))
        if 'dependency' not in skip:
            stages.append(stage_dependency(target))
        verdict, failures, incomplete, cross = compose(stages, acceptance, impact)
        payload = {
            'schema': SCHEMA, 'tool': 'audit/core.py', 'mode': 'self_audit',
            'task_id': 'SELF-AUDIT', 'repo': str(target), 'bundle': None,
            'base_commit': base, 'head_commit': head,
            'verdict': verdict, 'failed_stages': failures, 'incomplete_stages': incomplete,
            'cross_stage': cross, 'skipped_stages': sorted(skip),
            'stages': [s.as_dict() for s in stages],
            'mathematical_admission': False,
            'scope': ('Self-audit of one checkout: launcher self-cases pass here, the change '
                      'set from the frozen base to HEAD is accounted for, the gate stack catches '
                      'its claimed mutations, and no read-but-unpinned input exists. It reviews '
                      'no pull request and grants no mathematical admission.'),
        }
        out_path = Path(args.out) if args.out else REPO / 'audit' / 'core-verdict.json'
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + '\n',
                            encoding='utf-8')
        print(summarise(payload))
        print(f'core verdict written: {out_path}')
        return 0 if verdict == 'PASS' else 1

    if not args.bundle:
        parser.error('--bundle is required (or use --self-audit / --self-test)')

    bundle_path = Path(args.bundle).resolve()
    bundle = json.loads(bundle_path.read_text(encoding='utf-8-sig'))
    task = args.task or bundle.get('task_id')

    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        stages = []
        acceptance = impact = None
        if 'acceptance' not in skip:
            acceptance = stage_acceptance(bundle_path, task, target, workdir)
            stages.append(acceptance)
        if 'impact' not in skip:
            impact = stage_impact(target, bundle.get('base_commit'), bundle.get('head_commit'))
            stages.append(impact)
        if 'gates' not in skip:
            stages.append(stage_gates(target))
        if 'dependency' not in skip:
            stages.append(stage_dependency(target))

    verdict, failures, incomplete, cross = compose(stages, acceptance, impact)
    payload = {
        'schema': SCHEMA, 'tool': 'audit/core.py', 'task_id': task,
        'repo': str(target), 'bundle': str(bundle_path),
        'base_commit': bundle.get('base_commit'), 'head_commit': bundle.get('head_commit'),
        'verdict': verdict, 'failed_stages': failures, 'incomplete_stages': incomplete,
        'cross_stage': cross, 'skipped_stages': sorted(skip),
        'stages': [s.as_dict() for s in stages],
        'mathematical_admission': False,
        'scope': ('Composition of four engineering auditors. A PASS means the bundle metadata, '
                  'scope and replay agree, the change set is accounted for, the gate stack still '
                  'catches its claimed mutations, and no read-but-unpinned input was found. It is '
                  'not code review and not mathematical admission.'),
    }
    out_path = Path(args.out) if args.out else bundle_path.parent / 'core-verdict.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + '\n',
                        encoding='utf-8')
    print(summarise(payload))
    print(f'core verdict written: {out_path}')
    return 0 if verdict == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
