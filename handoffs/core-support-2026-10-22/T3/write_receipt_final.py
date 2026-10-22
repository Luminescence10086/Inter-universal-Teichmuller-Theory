"""Finalise the T3 editor receipt after the library-root module made the editor path work."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
T3 = ROOT / 'handoffs/core-support-2026-10-22/T3'
AFTER = T3 / 'after-root'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


INFO = {
    'localLog_eq_padicLog': 69,
    'summable_logTerm': 70,
    'hasSum_logTerm_localLog': 71,
    'logImage_Q3_eq_closedBall': 72,
}
MSG = ('Imports are out of date and must be rebuilt; use the "Restart File" command in your '
       'editor.')

receipt = {
    'schema': 1,
    'recorded_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    'observer': 'this session, Windows UI Automation (no computer-use service, no screenshots)',
    'editor': {'product': 'Visual Studio Code 1.143.0',
               'lean_extension': 'leanprover.lean4-0.0.240'},
    'editor_status': 'EDITOR_CHECKED',
    'scope_of_the_check': ('zero error and zero warning diagnostics for '
                           'candidates/core-transport/DelegatedLogBridge.lean, observed in a '
                           'trusted window with the Lean 4 extension active'),
    'diagnostics_observed': {'errors': 0, 'warnings': 0, 'information': 4},
    'information_items': [
        {'theorem': name, 'line': line,
         'text': ("'DelegatedLogBridge.%s' depends on axioms: [propext, Classical.choice, "
                  "Quot.sound]" % name)}
        for name, line in INFO.items()],
    'status_bar': {'information': '信息: 4 条', 'errors': 'absent', 'warnings': 'absent'},
    'before_fix': {
        'errors': 1, 'warnings': 0, 'message': MSG, 'position': 'line 1, character 1',
        'kind': 'extension stale-imports guard, not a Lean elaboration error',
        'evidence': 'vscode-problems-before-root.txt',
    },
    'root_cause_and_fix': {
        'cause': ('lean_lib CoreTransport was declared without the CoreTransport.lean library '
                  'root, so lake build failed and the extension could not obtain a build plan'),
        'fix': 'added candidates/core-transport/CoreTransport.lean (imports only, declares nothing)',
        'authorisation': ('outside T3\'s permitted-source rule; authorised explicitly by the '
                          'user on 2026-10-23 with the instruction to label it clearly, which the '
                          'file header does'),
        'lake_build_before': {'exit': 1, 'message': 'no such file or directory: CoreTransport.lean'},
        'lake_build_after': {'exit': 0, 'jobs': 2672},
        'cli_entry_rerun_after_fix': {'exit': 0, 'aims': 'unchanged four axiom lines'},
    },
    'not_observed': [
        'InfoView "No goals" for any declaration: the Infoview is an embedded webview whose text '
        'is not exposed in the accessibility tree (the same limitation recorded in '
        'local-phase earlier rounds, e.g. local-field/verification/round5-ui-partial-luna.txt)',
    ],
    'inputs': {
        'candidates/core-transport/DelegatedLogBridge.lean':
            sha(ROOT / 'candidates/core-transport/DelegatedLogBridge.lean'),
        'candidates/core-transport/CoreTransport.lean':
            sha(ROOT / 'candidates/core-transport/CoreTransport.lean'),
    },
    'evidence': {str(p.relative_to(T3)).replace('\\', '/'): sha(p) for p in [
        T3 / 'vscode-observation-before-root.txt', T3 / 'vscode-problems-before-root.txt',
        AFTER / 'vscode-observation-tree-2.txt', AFTER / 'vscode-problems-panel.txt',
        T3 / 't3-lake-build-after-root.stdout.txt', T3 / 'lean_stdout-after-root.txt',
        T3 / 'editor-check.md']},
    'fact_tree_admitted': False,
}
(T3 / 'vscode-receipt.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

delivery = json.load(io.open(T3 / 'delivery.json', encoding='utf-8'))
delivery['editor_status'] = 'EDITOR_CHECKED'
delivery['status'] = 'PARTIAL'
delivery['completed'].append(
    'after adding the labelled library-root module, the editor reports 0 errors and 0 warnings; '
    'the four remaining Problems entries are the #print axioms information messages themselves')
delivery['completed'].append(
    'lake build CoreTransport now exits 0 (2672 jobs) and the T3 entry re-runs at exit 0 with the '
    'same four axiom lines')
delivery['open'] = [
    'InfoView No goals was not observed for any declaration (Infoview webview text is not exposed '
    'through the accessibility tree)',
    'candidates/core-transport/CoreTransport.lean is outside T3\'s permitted-source rule; it was '
    'authorised by the user on 2026-10-23 and is labelled as a structural fix in its header',
]
delivery['outputs'] = [
    {'path': str(p.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(p)}
    for p in sorted(T3.rglob('*')) if p.is_file() and p.name != 'delivery.json']
(T3 / 'delivery.json').write_text(
    json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('status', delivery['status'], '| editor', delivery['editor_status'],
      '| outputs', len(delivery['outputs']))
print('receipt sha256', sha(T3 / 'vscode-receipt.json'))
print('root module sha256', sha(ROOT / 'candidates/core-transport/CoreTransport.lean'))
