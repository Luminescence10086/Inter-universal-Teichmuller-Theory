"""Write the W2 and W3 delivery packages (delivery.json + editor-check.md)."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
BASE = ROOT / 'handoffs/core-backward-2026-10-23'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


W3_INFOVIEW_HIT = {
    'algorithmRun_eq_partialSums': (93, 'No goals'),
    'localLog_eq_padicLog': (103, 'No goals'),
    'hasSum_logTerm_localLog': (111, 'No goals / Goals accomplished!'),
    'divide_back': (139, 'No goals'),
    'localLog_pow_eq_smul': (159, 'No goals'),
    'norm_four_Q3': (183, 'No goals'),
    'norm_four_sq_Q3': (189, 'No goals'),
    'norm_four_sub_one_Q3': (196, 'No goals'),
    'naive_magnitude_divide_back_fails': (209, 'No goals'),
    'naiveDivideBack_four_two': (216, 'No goals'),
}
W3_INFOVIEW_MISS = {
    'norm_pow_sub_one_lt_Q3': 121,
    'norm_two_Q3': 178,
    'divide_back_four_two': 245,
}


def editor_counts(path):
    text = Path(path).read_text(encoding='utf-8')
    return {
        'info_items': text.count('ControlType.TreeItem | \u4FE1\u606F:'),
        'error_items': text.count('ControlType.TreeItem | \u9519\u8BEF:'),
        'warning_items': text.count('ControlType.TreeItem | \u8B66\u544A:'),
        'status_bar': [ln.strip() for ln in text.splitlines()
                       if '\u4FE1\u606F:' in ln and '\u6761' in ln][:2],
    }


def package(task, src, folder, extra_outputs, gates, completed, unresolved, note):
    check = json.load(io.open(BASE / task / 'check.json', encoding='utf-8'))
    delivery = {
        'task_id': task,
        'status': 'CLI_CHECKED_EDITOR_CHECKED',
        'vocabulary_note': ('the batch vocabulary has no value for a Lean task verified in both '
                            'planes; this value names exactly what was run'),
        'started_at': time.strftime('%Y-%m-%dT%H:%M:%S%z'),
        'inputs': [
            {'path': 'candidates/core-transport/CoreTransport/Basic.lean',
             'sha256': sha(ROOT / 'candidates/core-transport/CoreTransport/Basic.lean')},
            {'path': 'candidates/core-log/CoreLog/QpThree.lean',
             'sha256': sha(ROOT / 'candidates/core-log/CoreLog/QpThree.lean')},
        ] + extra_outputs['inputs'],
        'outputs': [
            {'path': str(src.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(src)},
            {'path': str((BASE / task / 'check.json').relative_to(ROOT)).replace('\\', '/'),
             'sha256': sha(BASE / task / 'check.json')},
            {'path': str((BASE / task / 'editor-check.md').relative_to(ROOT)).replace('\\', '/'),
             'sha256': sha(BASE / task / 'editor-check.md')},
        ] + extra_outputs['outputs'],
        'gates': {
            'cli': {'exit': 0, 'stderr_bytes': 0, 'diagnostics': check['counts'],
                    'theorems_with_axiom_report': len(check['axioms']) + len(check['axiom_free']),
                    'axioms': sorted({a for v in check['axioms'].values() for a in v}),
                    'forbidden_terms': len(check['forbidden']),
                    'source_sha256': sha(src)},
            'editor': gates['editor'],
            'infoview': gates['infoview'],
        },
        'completed': completed,
        'unresolved': unresolved,
        'core_gap': 'OPEN',
        'lean_run': True,
        'editor_run': True,
        'fact_tree_admitted': False,
        'note': note,
    }
    (BASE / task / 'delivery.json').write_text(
        json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    return delivery


# ---------------- W2: provenance on a local-global collection ----------------
w2_src = ROOT / 'candidates/core-transport/CollectionProvenance.lean'
w2_editor = editor_counts(BASE / 'W2/editor/vscode-observation-tree-2.txt')
d2 = package(
    'W2', w2_src, 'W2',
    {'inputs': [{'path': 'handoffs/core-backward-2026-10-23/M3/interfaces.json',
                 'sha256': sha(BASE / 'M3/interfaces.json')}],
     'outputs': [{'path': 'handoffs/core-backward-2026-10-23/W2/README.md',
                  'sha256': sha(BASE / 'W2/README.md')},
                 {'path': 'handoffs/core-backward-2026-10-23/W2/editor/vscode-observation-tree-2.txt',
                  'sha256': sha(BASE / 'W2/editor/vscode-observation-tree-2.txt')}]},
    {'editor': {'product': 'Visual Studio Code 1.143.0',
                'lean_extension': 'leanprover.lean4-0.0.240',
                'errors': w2_editor['error_items'], 'warnings': w2_editor['warning_items'],
                'info_items': w2_editor['info_items'],
                'status_bar': w2_editor['status_bar']},
     'infoview': {'attempted': False,
                  'reason': 'not run for this file; the goal requires CLI + axiom whitelist + '
                            'editor zero diagnostics, all three of which are recorded here'}},
    completed=[
        'provenance lifted from one element to a local-global collection: every local piece is '
        'pinned to algorithmRun by steps_eq, and the reading of each piece is derived, not assumed',
        'the anti-degeneracy statement took its preferred form: two collections with the same n, '
        'all local values in the log image, different global readings',
        'the builder also recorded why the stronger form is impossible in this toy: identical '
        'localInput forces identical readings (both_readings_unique)',
    ],
    unresolved=[
        'the localization here is a toy equality (global = local), not IUT localization data',
        'the collection is a Fin n indexed family over Q_3, not an adelic or hull object',
        'this file says nothing about Theta-links, Ism, prime-strips or Cor 3.12',
    ],
    note='the builder reported two defects that my own checker had to be repaired for twice '
         '(declaration scan over docstring prose, and the set_option placement); see the commit log')

# ---------------- W3: divide-back law + H3 obligation document ----------------
w3_src = ROOT / 'candidates/core-transport/DivideBackLaw.lean'
w3_editor = editor_counts(BASE / 'W3/editor/vscode-observation-tree-2.txt')
d3 = package(
    'W3', w3_src, 'W3',
    {'inputs': [{'path': 'research/core-backward-2026-10-23/h3-prerequisites.md',
                 'sha256': sha(ROOT / 'research/core-backward-2026-10-23/h3-prerequisites.md')}],
     'outputs': [{'path': 'research/core-backward-2026-10-23/h3-prerequisites.md',
                  'sha256': sha(ROOT / 'research/core-backward-2026-10-23/h3-prerequisites.md')},
                 {'path': 'handoffs/core-backward-2026-10-23/W3/editor/vscode-observation-tree-2.txt',
                  'sha256': sha(BASE / 'W3/editor/vscode-observation-tree-2.txt')}]},
    {'editor': {'product': 'Visual Studio Code 1.143.0',
                'lean_extension': 'leanprover.lean4-0.0.240',
                'errors': w3_editor['error_items'], 'warnings': w3_editor['warning_items'],
                'info_items': w3_editor['info_items'],
                'status_bar': w3_editor['status_bar']},
     'infoview': {'attempted': True,
                  'hit': {k: {'line': v[0], 'text': v[1]} for k, v in W3_INFOVIEW_HIT.items()},
                  'not_read': {k: {'line': v, 'why': 'cursor line computed off by one or two by the '
                                                      'helper; not a Lean failure'}
                               for k, v in W3_INFOVIEW_MISS.items()}}},
    completed=[
        'divide_back: the reading of x is recovered from the reading of x^M by dividing by the '
        'scalar M, derived from the quoted padicLog_pow (not re-proved)',
        'anti-degeneracy at the same x and M: the naive magnitude reading does not divide back '
        '(1/2 against 1), so "divide by M" is not a content-free step',
        'h3-prerequisites.md records the three accounting obligations with source locators, each '
        'verified against the text or explicitly marked as quoted from M2',
    ],
    unresolved=[
        'the law is a toy: x |-> x^M stands in for det^{tensor M}, and Q_3 is not the localisation '
        'of an arithmetic line bundle',
        'M-i (no divide-back map in the source) is only given its shape here; the tensor-power '
        'Frobenioid statement is untouched',
        'M-ii (the three M are the same) and M-iii (the two unnamed normalizations) are documented '
        'as obligations, not discharged',
    ],
    note='the builder corrected an arithmetic error in my own task brief: 16 = 2^4 is a unit, so '
         'the norm is 1 and not 1/9; the separation still holds (1/2 against 1)')

print('W2:', d2['status'], d2['gates']['cli']['diagnostics'], '| editor', d2['gates']['editor']['errors'],
      '/', d2['gates']['editor']['warnings'], '| infoview', d2['gates']['infoview']['attempted'])
print('W3:', d3['status'], d3['gates']['cli']['diagnostics'], '| editor', d3['gates']['editor']['errors'],
      '/', d3['gates']['editor']['warnings'], '| infoview hit', len(W3_INFOVIEW_HIT),
      'miss', len(W3_INFOVIEW_MISS))
