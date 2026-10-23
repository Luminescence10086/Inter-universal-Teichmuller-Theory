"""Write the W1 delivery package."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
W1 = ROOT / 'handoffs/core-backward-2026-10-23/W1'
SRC = ROOT / 'candidates/core-transport/ReadingInvariance.lean'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


INFO = {
    'localLog_eq_padicLog': 66,
    'hasSum_logTerm_localLog': 75,
    'partialSumAlong_one': 87,
    'hasSum_perm': 100,
    'reading_independent_of_enumeration': 108,
    'logTerm_four_zero': 115,
    'logTerm_four_two': 120,
    'norm_nine': 127,
    'partialSum_not_invariant': 152,
}

check = json.load(io.open(W1 / 'check.json', encoding='utf-8'))

delivery = {
    'task_id': 'W1',
    'status': 'CLI_CHECKED_EDITOR_CHECKED',
    'vocabulary_note': ('the batch vocabulary (STATIC_ONLY / PARTIAL / INPUT_DRIFT) has no value for a '
                        'Lean task verified in both planes; this value names exactly what was run'),
    'started_at': time.strftime('%Y-%m-%dT%H:%M:%S%z'),
    'inputs': [
        {'path': 'research/core-backward-2026-10-23/h1-decision.md', 'sha256': sha(ROOT / 'research/core-backward-2026-10-23/h1-decision.md')},
        {'path': 'handoffs/core-backward-2026-10-23/M3/interfaces.json', 'sha256': sha(ROOT / 'handoffs/core-backward-2026-10-23/M3/interfaces.json')},
        {'path': 'candidates/core-transport/CoreTransport/Basic.lean', 'sha256': sha(ROOT / 'candidates/core-transport/CoreTransport/Basic.lean')},
        {'path': 'candidates/core-log/CoreLog/QpThree.lean', 'sha256': sha(ROOT / 'candidates/core-log/CoreLog/QpThree.lean')},
    ],
    'outputs': [
        {'path': 'candidates/core-transport/ReadingInvariance.lean', 'sha256': sha(SRC)},
        {'path': 'handoffs/core-backward-2026-10-23/W1/README.md', 'sha256': sha(W1 / 'README.md')},
        {'path': 'handoffs/core-backward-2026-10-23/W1/check.json', 'sha256': sha(W1 / 'check.json')},
        {'path': 'handoffs/core-backward-2026-10-23/W1/editor-check.md', 'sha256': sha(W1 / 'editor-check.md')},
        {'path': 'handoffs/core-backward-2026-10-23/W1/editor/vscode-observation-tree-2.txt', 'sha256': sha(W1 / 'editor/vscode-observation-tree-2.txt')},
    ],
    'gates': {
        'cli': {'argv': ['lake', 'env', 'lean', '-DwarningAsError=true', 'ReadingInvariance.lean'],
                'cwd': 'candidates/core-transport', 'exit': 0, 'stderr_bytes': 0,
                'diagnostics': check['counts'], 'theorems_with_axiom_report': 10,
                'axioms': sorted({a for v in check['axioms'].values() for a in v}),
                'forbidden_terms': 0, 'rechecked_on_source_sha': sha(SRC)[:16]},
        'editor': {'product': 'Visual Studio Code 1.143.0',
                   'lean_extension': 'leanprover.lean4-0.0.240',
                   'errors': 0, 'warnings': 0, 'information': 24,
                   'status_bar': 'info 24 lines only, no error or warning counter'},
        'infoview': {'per_declaration': {k: {'line': v, 'text': 'No goals'} for k, v in INFO.items()},
                     'method': '--force-renderer-accessibility; cursor after the last tactic step',
                     'evidence_dir': 'handoffs/core-backward-2026-10-23/W1/infoview/'},
    },
    'completed': [
        'hasSum_perm: the reading is the same under any enumeration, quoted from Equiv.hasSum_iff '
        'on top of the existing convergence theorem',
        'reading_independent_of_enumeration: two presentations give the same tsum, both sides kept as tsum',
        'partialSum_not_invariant: concrete witness (swap 0 2, n = 1, x = 4) separating 9 from 3 by norm',
        'all three gates passed; 9/9 Infoview zero-goal',
    ],
    'unresolved': [
        'this is an analogue of Ind1-3, not Ind1-3: the presentation is a step enumeration, not a Theta-link '
        'indeterminacy, and no Theta-link, Ism, prime-strip, Hodge theater or coricity is constructed',
        'section 1-prime of h1-decision is NOT discharged for the real object',
        'reading_independent_of_enumeration permutes only the enumeration at fixed x; independence of the '
        'choice of x is not proved',
        'the editor capture script had a mojibake defect in its restricted-mode check; fixed here, and the '
        'effect on the T3/K4 receipts is recorded in editor-check.md',
    ],
    'core_gap': 'OPEN',
    'lean_run': True,
    'editor_run': True,
    'fact_tree_admitted': False,
}
(W1 / 'delivery.json').write_text(
    json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('status:', delivery['status'], '| gates:', delivery['gates']['cli']['diagnostics'],
      '| axioms:', delivery['gates']['cli']['axioms'])
print('source sha:', sha(SRC))
print('outputs:', len(delivery['outputs']))
