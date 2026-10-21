"""Self-tests for the core composer (audit/core.py).

Run directly or through `python -B audit/core.py --self-test`. Each case builds the
minimal data it needs, patches only the composer's own process boundary, and asserts the
verdict algebra plus the two composition checks that no single auditor can make.
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
CORE_PATH = HERE / 'core.py'


def load_core():
    spec = importlib.util.spec_from_file_location('core_under_test', str(CORE_PATH))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def make_stage(core, name, status, data=None):
    stage = core.Stage(name)
    stage.status = status
    stage.detail = 'fixture'
    stage.data = data or {}
    return stage


def fake_run_for(core, payload):
    def fake(argv, cwd, timeout):
        return {'exit': 0, 'stdout': json.dumps(payload), 'stderr': '',
                'seconds': 0.01, 'timed_out': False}
    core.run = fake
    core.tool_for = lambda stage, repo: (CORE_PATH, None)


CASES = {}


def case(name):
    def register(fn):
        CASES[name] = fn
        return fn
    return register


@case('CORE.all_pass_is_pass')
def _all_pass():
    core = load_core()
    stages = [make_stage(core, n, 'PASS') for n in core.STAGES]
    verdict, failures, incomplete, cross = core.compose(stages, stages[0], stages[1])
    assert verdict == 'PASS' and not failures and not incomplete and not cross


@case('CORE.any_fail_is_fail')
def _fail():
    core = load_core()
    stages = [make_stage(core, n, 'PASS') for n in core.STAGES]
    stages[2].status = 'FAIL'
    verdict, failures, _, _ = core.compose(stages, stages[0], stages[1])
    assert verdict == 'FAIL' and failures == ['gates'], (verdict, failures)


@case('CORE.incomplete_never_rounds_up')
def _incomplete():
    core = load_core()
    stages = [make_stage(core, n, 'PASS') for n in core.STAGES]
    stages[1].status = 'INCOMPLETE'
    verdict, _, incomplete, _ = core.compose(stages, stages[0], stages[1])
    assert verdict == 'INCOMPLETE' and incomplete == ['impact']


@case('CORE.accepted_bundle_that_voids_its_receipt_is_not_pass')
def _cross_stage():
    core = load_core()
    acceptance = make_stage(core, 'acceptance', 'PASS')
    impact = make_stage(core, 'impact', 'PASS', {'receipts_voided': 1, 'receipts_unknown': 0})
    stages = [acceptance, impact]
    verdict, failures, _, cross = core.compose(stages, acceptance, impact)
    assert verdict == 'FAIL' and 'cross-stage' in failures and cross, (verdict, failures)


@case('CORE.impact_internal_inconsistency_fails')
def _under_report():
    core = load_core()
    fake_run_for(core, {'counts': {'receipts_voided': 0, 'receipts_unknown': 0,
                                   'snapshot_members_added': 1},
                        'changed': ['bridge/IUTBridge/NewCandidate.lean'],
                        'snapshot_membership': {'probe': 'enabled', 'entry_points': {}},
                        'contracts': {'invalidated': 0}, 'warnings': []})
    stage = core.stage_impact(HERE, 'a' * 40, 'b' * 40)
    assert stage.status == 'FAIL' and 'inconsistent' in stage.detail, stage.detail


@case('CORE.impact_undecided_membership_is_incomplete')
def _impact_undecided():
    core = load_core()
    fake_run_for(core, {'counts': {'receipts_voided': 0, 'receipts_unknown': 0,
                                   'snapshot_members_added': 0},
                        'changed': ['bridge/IUTBridge/NewCandidate.lean'],
                        'snapshot_membership': {'probe': 'disabled', 'entry_points': {}},
                        'contracts': {'invalidated': 0}, 'warnings': []})
    stage = core.stage_impact(HERE, 'a' * 40, 'b' * 40)
    assert stage.status == 'INCOMPLETE', stage.status


@case('CORE.impact_unknown_is_incomplete')
def _impact_unknown():
    core = load_core()
    fake_run_for(core, {'counts': {'receipts_voided': 0, 'receipts_unknown': 2,
                                   'snapshot_members_added': 0},
                        'changed': ['bridge/IUTBridge/NewCandidate.lean'],
                        'snapshot_membership': {'probe': 'enabled', 'entry_points': {}},
                        'contracts': {'invalidated': 0}, 'warnings': []})
    stage = core.stage_impact(HERE, 'a' * 40, 'b' * 40)
    assert stage.status == 'INCOMPLETE', stage.status


@case('CORE.read_but_unpinned_input_fails')
def _under_pinned():
    core = load_core()
    fake_run_for(core, [{'project': 'bridge', 'counts': {'under_pinned': 1, 'unclassified': 3},
                         'closure': {'status': 'incomplete'}}])
    stage = core.stage_dependency(HERE)
    assert stage.status == 'FAIL' and 'not pinned' in stage.detail, stage.detail


@case('CORE.withheld_proposal_is_informational')
def _withheld():
    core = load_core()
    fake_run_for(core, [{'project': 'bridge', 'counts': {'under_pinned': 0, 'unclassified': 20},
                         'closure': {'status': 'incomplete'}}])
    stage = core.stage_dependency(HERE)
    assert stage.status == 'PASS', stage.status


@case('CORE.empty_composition_is_incomplete')
def _empty():
    core = load_core()
    verdict, failures, incomplete, cross = core.compose([], None, None)
    assert verdict == 'INCOMPLETE' and cross, (verdict, cross)


@case('CORE.self_audit_smoke')
def _self_audit():
    import tempfile
    core = load_core()
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / 'core.json'
        code = core.main(['--self-audit', '--repo', str(core.REPO),
                          '--skip', 'impact,gates,dependency', '--out', str(out)])
        payload = json.loads(out.read_text(encoding='utf-8'))
    assert code == 0, code
    assert payload['mode'] == 'self_audit' and payload['verdict'] == 'PASS', payload.get('verdict')
    assert payload['stages'][0]['stage'] == 'acceptance'


@case('CORE.stage_tools_present')
def _tools_present():
    core = load_core()
    missing = [str(path) for path in core.TOOL_PATHS.values() if not (core.REPO / path).exists()]
    assert not missing, missing
    for path in core.TOOL_PATHS.values():
        result = subprocess.run([sys.executable, '-B', str(core.REPO / path), '--help'],
                                capture_output=True, timeout=120)
        assert result.returncode == 0, (str(path), result.returncode)


def main(argv):
    selected = argv or list(CASES)
    failures = []
    for name in selected:
        if name not in CASES:
            print(f'UNKNOWN {name}')
            failures.append(name)
            continue
        try:
            CASES[name]()
            print(f'PASS {name}')
        except AssertionError as exc:
            print(f'FAIL {name}: {exc}')
            failures.append(name)
        except Exception as exc:  # noqa: BLE001 - a crashing case is a failure
            print(f'ERROR {name}: {type(exc).__name__}: {exc}')
            failures.append(name)
    print(f'{len(selected) - len(failures)}/{len(selected)} composition cases ok')
    return 0 if not failures else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
