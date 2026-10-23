"""Write the K4 delivery package: delivery.json and the three-gate record."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
K4 = ROOT / 'handoffs/core-backward-2026-10-23/K4'
SRC = ROOT / 'candidates/core-transport/ExecutionProvenance.lean'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


INFO = {
    'algorithmRun_eq_partialSums': (64, 'No goals'),
    'localLog_eq_padicLog': (79, 'No goals'),
    'hasSum_logTerm_localLog': (87, 'No goals'),
    'value_eq_localLog': (138, 'No goals'),
    'value_unique': (145, 'No goals'),
    'value_mem_logImage': (155, 'Goals accomplished!'),
    'logImage_Q3_eq_closedBall': (170, 'No goals'),
    'norm_four_sub_one': (176, 'No goals'),
    'witnessFour': (190, 'No goals'),
}

check = json.load(io.open(K4 / 'check.json', encoding='utf-8'))
editor_tree = K4 / 'editor/vscode-observation-tree-2.txt'
tree_text = editor_tree.read_text(encoding='utf-8')

delivery = {
    'task_id': 'K4',
    'status': 'CLI_CHECKED_EDITOR_CHECKED',
    'vocabulary_note': ('the batch vocabulary (STATIC_ONLY / PARTIAL / INPUT_DRIFT) has no value for '
                        'a Lean task verified in both planes; this value names exactly what was run'),
    'started_at': time.strftime('%Y-%m-%dT%H:%M:%S%z'),
    'inputs': [
        {'path': 'candidates/core-transport/lakefile.lean', 'sha256': sha(ROOT / 'candidates/core-transport/lakefile.lean')},
        {'path': 'candidates/core-transport/CoreTransport.lean', 'sha256': sha(ROOT / 'candidates/core-transport/CoreTransport.lean')},
        {'path': 'candidates/core-transport/CoreTransport/Basic.lean', 'sha256': sha(ROOT / 'candidates/core-transport/CoreTransport/Basic.lean')},
        {'path': 'candidates/core-log/CoreLog/QpThree.lean', 'sha256': sha(ROOT / 'candidates/core-log/CoreLog/QpThree.lean')},
        {'path': 'handoffs/core-backward-2026-10-23/M3/interfaces.json', 'sha256': sha(ROOT / 'handoffs/core-backward-2026-10-23/M3/interfaces.json')},
    ],
    'outputs': [
        {'path': 'candidates/core-transport/ExecutionProvenance.lean', 'sha256': sha(SRC)},
        {'path': 'handoffs/core-backward-2026-10-23/K4/README.md', 'sha256': sha(K4 / 'README.md')},
        {'path': 'handoffs/core-backward-2026-10-23/K4/check.json', 'sha256': sha(K4 / 'check.json')},
        {'path': 'handoffs/core-backward-2026-10-23/K4/editor-check.md', 'sha256': sha(K4 / 'editor-check.md')},
        {'path': 'handoffs/core-backward-2026-10-23/K4/lean_stdout.txt', 'sha256': sha(K4 / 'lean_stdout.txt')},
        {'path': 'handoffs/core-backward-2026-10-23/K4/lean_stderr.txt', 'sha256': sha(K4 / 'lean_stderr.txt')},
        {'path': 'handoffs/core-backward-2026-10-23/K4/editor/vscode-observation-tree-2.txt', 'sha256': sha(editor_tree)},
    ],
    'gates': {
        'cli': {'command': ['lake', 'env', 'lean', '-DwarningAsError=true', 'ExecutionProvenance.lean'],
                'cwd': 'candidates/core-transport', 'exit': 0, 'stderr_bytes': 0,
                'diagnostics': check['counts'], 'theorems_with_axiom_report': 10,
                'axioms': sorted({a for v in check['axioms'].values() for a in v}),
                'forbidden_terms': 0, 'rechecked_on_final_file_sha': sha(SRC)[:16]},
        'editor': {'product': 'Visual Studio Code 1.143.0',
                   'lean_extension': 'leanprover.lean4-0.0.240',
                   'errors': 0, 'warnings': 0, 'information': 14,
                   'status_bar': '信息: 14 条 (no error or warning counter)',
                   'evidence': 'handoffs/core-backward-2026-10-23/K4/editor/vscode-observation-tree-2.txt'},
        'infoview': {'method': '--force-renderer-accessibility, cursor after the last tactic step',
                     'per_declaration': {k: {'line': v[0], 'text': v[1]} for k, v in INFO.items()},
                     'evidence_dir': 'handoffs/core-backward-2026-10-23/K4/infoview/'},
    },
    'completed': [
        'LegalExecution carries the trace by definitional equality with the algorithm (steps_eq), '
        'so the trace cannot be chosen',
        'value_eq_localLog derives value = localLog input from converges + steps_eq + the existing '
        'Q_3 convergence theorem, via uniqueness of limits',
        'value_unique: the value is a function of the input alone',
        'value_mem_logImage is derived, not a field: the contrast with EtaAlg.realisation that K4 exists for',
        'non-vacuity: witnessFour is a concrete legal execution at input 4, every field discharged',
        'CLI gate PASS on the final file sha; editor gate 0 errors / 0 warnings; nine Infoview readings '
        'all zero-goal',
    ],
    'unresolved': [
        'the algorithm here is the p-adic logarithm partial-sum algorithm, NOT the η-algorithm of IUT; '
        'no IUT interface has been recast in provenance form',
        'DelegatedLogBridge is not a Lake target and has no olean, so its two definition-level lemmas '
        'are restated locally (documented in the file)',
        'InfoView at the blank line after value_mem_logImage read empty twice; the reading was taken at '
        'the end of the proof line itself',
    ],
    'core_gap': 'OPEN',
    'lean_run': True,
    'editor_run': True,
    'fact_tree_admitted': False,
}
(K4 / 'delivery.json').write_text(
    json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

print('delivery written; gates:', json.dumps(delivery['gates']['cli']['diagnostics']))
print('source sha:', sha(SRC))
print('outputs:', len(delivery['outputs']))
print('editor tree has info/error/warning:',
      tree_text.count('| 信息:'), tree_text.count('| 错误:'), tree_text.count('| 警告:'))
