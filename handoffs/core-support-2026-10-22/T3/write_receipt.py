"""Write the T3 editor receipt and fold the editor outcome into delivery.json.

Kept as a file rather than an inline -c string because the diagnostic text itself contains
quotes and backslashes, and inline quoting repeatedly mangled it.
"""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
T3 = ROOT / 'handoffs' / 'core-support-2026-10-22' / 'T3'
MSG = ('Imports are out of date and must be rebuilt; use the "Restart File" command in your '
       'editor.')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


receipt = {
    'schema': 1,
    'recorded_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    'observer': 'this session, Windows UI Automation (no computer-use service, no screenshots)',
    'editor': {'product': 'Visual Studio Code 1.143.0',
               'lean_extension': 'leanprover.lean4-0.0.240'},
    'editor_status': 'PARTIAL',
    'zero_diagnostics_claimed': False,
    'windows_observed': ['core-transport - Visual Studio Code',
                         'core-log - Visual Studio Code'],
    'trust': ('granted through the Restricted Mode banner (manage -> trust); no user settings '
              'were edited'),
    'diagnostics_observed': {
        'candidates/core-transport/DelegatedLogBridge.lean': {
            'errors': 1, 'warnings': 0, 'message': MSG,
            'position': 'line 1, character 1',
            'kind': 'extension stale-imports guard, not a Lean elaboration error'},
        'candidates/core-log/CoreLog/QpThree.lean': {
            'errors': 1, 'warnings': 0, 'same_message': True},
    },
    'causal_evidence': {
        'lake_build_core_transport_exit': 1,
        'lake_build_core_transport_message': ('no such file or directory: '
                                             'candidates/core-transport/CoreTransport.lean '
                                             '(lean_lib declares a root module that does not exist)'),
        'lake_build_core_log_exit': 0,
        'lake_build_core_log_jobs': 3047,
        'note': ('core-log builds cleanly yet the guard persists, so a failed build is not the '
                 'only cause'),
    },
    'inputs': {
        'candidates/core-transport/DelegatedLogBridge.lean':
            sha(ROOT / 'candidates/core-transport/DelegatedLogBridge.lean'),
        'candidates/core-log/CoreLog/QpThree.lean':
            sha(ROOT / 'candidates/core-log/CoreLog/QpThree.lean'),
    },
    'evidence': {rel: sha(T3 / rel) for rel in [
        'vscode-observation-tree-2.txt', 'vscode-problems-panel.txt',
        'corelog/vscode-observation-tree-2.txt', 'corelog/vscode-problems-panel.txt',
        'vscode-observation-attempt1-INVALID.txt',
        't3-lake-build-CoreTransport.stdout.txt', 'editor-check.md']},
    'not_observed': ['zero error/warning counts',
                     'InfoView No goals for any T3 declaration'],
    'fact_tree_admitted': False,
}
(T3 / 'vscode-receipt.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

delivery = json.load(io.open(T3 / 'delivery.json', encoding='utf-8'))
delivery['editor_status'] = 'PARTIAL'
delivery['status'] = 'PARTIAL'
delivery['completed'].append(
    'editor opened in a trusted window with Lean 4 active; the single diagnostic was identified '
    'verbatim as the extension stale-imports guard, not an elaboration error')
delivery['completed'].append(
    'causal evidence: lake build CoreTransport fails on a missing library root module '
    'CoreTransport.lean')
delivery['open'].extend([
    'editor reports 1 error (0 warnings); no zero-diagnostic editor state was reached',
    'no InfoView No goals observation for the four declarations',
    'clearing the guard requires adding candidates/core-transport/CoreTransport.lean, which the '
    'T3 rules forbid',
])
delivery['outputs'] = [
    {'path': str(p.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(p)}
    for p in sorted(T3.rglob('*')) if p.is_file() and p.name != 'delivery.json']
(T3 / 'delivery.json').write_text(
    json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

print('status', delivery['status'], '| editor', delivery['editor_status'],
      '| outputs', len(delivery['outputs']))
print('receipt sha256', sha(T3 / 'vscode-receipt.json'))
