"""Assemble the R1-R4 fix record for research/lana-link-acceptance-2026-10-23/fix-handoff.md.

Three things happen here, and each one is idempotent so the script can be re-run after any further edit:

1. W9 and W10 `delivery.json` outputs are rebuilt. The R2 applier (`apply_r2_deliveries.py`) prepended
   the new source with an *absolute* path and left the stale entry behind, so the record listed the same
   file twice with two different hashes. The rebuild keeps one entry per path, relative, hash verified.
2. W11 `delivery.json` is corrected: the alignment hash is refreshed after the R1 rewrite of
   `lana-report-assessment.md`, and the editor gate is lowered to what the capture actually supports
   (see `handoffs/core-backward-2026-10-23/W11/editor/README.md`).
3. `fix-delivery.json` is written: per review item, the original commit, the new source hash, the
   commands that were run with their results, and the unresolved residue.
"""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
BASE = ROOT / 'handoffs/core-backward-2026-10-23'
REVIEW = ROOT / 'research/lana-link-acceptance-2026-10-23/fix-handoff.md'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rel(path):
    return str(Path(path).resolve().relative_to(ROOT)).replace('\\', '/')


def load(path):
    # PowerShell's `Set-Content -Encoding utf8` writes a BOM, which json rejects; read it away.
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def dump(path, obj):
    Path(path).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def commit_of(path):
    out = subprocess.run(['git', 'log', '--oneline', '-1', '--', str(path)],
                         cwd=ROOT, capture_output=True, text=True, encoding='utf-8')
    return out.stdout.strip()


# --- 1. rebuild the W9 / W10 outputs -------------------------------------------------------------

REBUILD = {
    'W9': ('candidates/core-transport/ExponentUniqueness.lean', 'ba78ff1'),
    'W10': ('candidates/core-transport/H3Synthesis.lean', '64126ef'),
}


def rebuild_outputs(task, source):
    p = BASE / task / 'delivery.json'
    d = load(p)
    extras = [rel(BASE / task / 'README.md'),
              rel(BASE / task / 'check.json'),
              rel(BASE / task / 'editor/vscode-observation-tree-2.txt')]
    wanted = [source] + extras
    d['outputs'] = [{'path': w, 'sha256': sha(ROOT / w)} for w in wanted if (ROOT / w).exists()]
    dump(p, d)
    return d


rebuilt = {}
for task, (source, original) in REBUILD.items():
    rebuilt[task] = rebuild_outputs(task, source)

# W8, W9 and W11 share the same defect: their editor trees contain no axiom row at all, so the
# EDITOR_CHECKED label was never supported by the file it cites. Lower all three the same way.
for task, commit in [('W8', None), ('W9', 'ba78ff1')]:
    p = BASE / task / 'delivery.json'
    d = load(p)
    if not d.get('gates', {}).get('editor'):
        continue
    d['status'] = 'CLI_CHECKED_EDITOR_PENDING'
    d['editor_run'] = False
    d['gates']['editor'] = {
        'product': 'Visual Studio Code 1.143.0',
        'lean_extension': 'leanprover.lean4-0.0.240',
        'errors': 'not attested by the editor',
        'warnings': 'not attested by the editor',
        'why': ('the cited tree (editor/vscode-observation-tree-2.txt) contains no "depends on axioms" row at '
                'all, so it cannot show that this file was elaborated; the reading that lowered W11 in R3 '
                'applies unchanged'),
        'evidence': 'editor/vscode-observation-tree-2.txt',
    }
    if commit:
        d.setdefault('review_fixes', []).append({
            'round': 'R3', 'original_commit': commit,
            'note': ('editor label lowered under the R3 reading: the evidence file holds no axiom row, so the '
                     'editor plane does not attest the file; CLI plane unchanged and re-verified after R2'),
            'new_source_sha256': sha(ROOT / 'candidates/core-transport/ExponentUniqueness.lean')})
    dump(p, d)
    if task in rebuilt:
        rebuilt[task] = d

# --- 2. W11 delivery -----------------------------------------------------------------------------

w11_path = BASE / 'W11/delivery.json'
w11 = load(w11_path)
assessment = 'research/core-backward-2026-10-23/lana-report-assessment.md'
path_doc = 'research/core-backward-2026-10-23/PATH.md'
w11['alignment_record'] = {
    'path': assessment,
    'sha256': sha(ROOT / assessment),
    'role': ('records the verbatim repository statements (EtaAlg.lean:145/151, Rss.lean:501) that this toy '
             'mirrors: maps of pointed lines are equal iff they agree at the pilot. Hash refreshed by R1, '
             'which rewrote its section 3 item 1.'),
}
w11['inputs'] = [{'path': assessment, 'sha256': sha(ROOT / assessment)},
                 {'path': 'handoffs/core-backward-2026-10-23/W7/delivery.json',
                  'sha256': sha(BASE / 'W7/delivery.json')}]
capture = load(BASE / 'W11/editor/capture-axiom-report.json')
w11['outputs'] = [
    {'path': 'candidates/core-transport/EtaComparison.lean',
     'sha256': sha(ROOT / 'candidates/core-transport/EtaComparison.lean')},
    {'path': 'handoffs/core-backward-2026-10-23/W11/check.json', 'sha256': sha(BASE / 'W11/check.json')},
    {'path': 'handoffs/core-backward-2026-10-23/W11/editor/vscode-observation-axioms.txt',
     'sha256': sha(BASE / 'W11/editor/vscode-observation-axioms.txt')},
    {'path': 'handoffs/core-backward-2026-10-23/W11/editor/capture-axiom-report.json',
     'sha256': sha(BASE / 'W11/editor/capture-axiom-report.json')},
    {'path': 'handoffs/core-backward-2026-10-23/W11/editor/capture-axiom-report.log',
     'sha256': sha(BASE / 'W11/editor/capture-axiom-report.log')},
    {'path': 'handoffs/core-backward-2026-10-23/W11/editor/README.md',
     'sha256': sha(BASE / 'W11/editor/README.md')},
]
w11['status'] = 'CLI_CHECKED_EDITOR_PENDING'
w11['editor_run'] = False
w11['gates']['editor'] = {
    'product': 'Visual Studio Code 1.143.0',
    'lean_extension': 'leanprover.lean4-0.0.240',
    'errors': 'not attested by the editor',
    'warnings': 'not attested by the editor',
    'what_the_editor_plane_shows': ('the window is core-transport, the open document is the absolute path of '
                                    'EtaComparison.lean, the Problems panel is filtered to that name and holds '
                                    'zero rows of any severity (banner: no results under the given filter), '
                                    'while the same panel holds 47 information rows belonging to other files'),
    'why_that_is_not_a_pass': ('zero rows for this file and 47 information rows for other files means the '
                               'extension did not elaborate this file: absence of rows is not a reading of '
                               'zero diagnostics'),
    'capture': 'editor/capture-axiom-report.json',
    'attempts_documented': 'editor/README.md',
    'evidence': 'editor/vscode-observation-axioms.txt',
}
w11.setdefault('review_fixes', []).extend([
    {'round': 'R1', 'original_commit': '909af74',
     'note': ('the claim that W5/W7 invariance is a necessary condition for (9-1) is withdrawn; the '
              'alignment record that carries the verbatim sources was rewritten accordingly'),
     'new_source_sha256': sha(ROOT / assessment)},
    {'round': 'R3', 'original_commit': '023c9a1',
     'note': ('the editor gate no longer rests on an empty Problems panel: four capture sessions are '
              'documented, the file was never elaborated in them, and the label is lowered to '
              'CLI_CHECKED_EDITOR_PENDING'),
     'capture_axiom_rows': capture['axiomRows'],
     'capture_error_rows': capture['errorOrWarningRows'],
     'capture_exit_code': 6},
])
dump(w11_path, w11)

# --- 3. the fix record ---------------------------------------------------------------------------

editor_sweep = {}
for task in ['K4', 'W1', 'W2', 'W3', 'W4', 'W5', 'W6', 'W7', 'W8', 'W9', 'W10', 'W11', 'W12']:
    tree = BASE / task / 'editor/vscode-observation-tree-2.txt'
    if tree.exists():
        editor_sweep[task] = (tree.read_text(encoding='utf-8', errors='replace').count('depends on axioms'))
    else:
        editor_sweep[task] = None

record = {
    'round': 'R1-R4',
    'review_of': {'path': rel(REVIEW), 'sha256': sha(REVIEW)},
    'produced_at': '2026-10-23',
    'branch': subprocess.run(['git', 'rev-parse', '--abbrev-ref', 'HEAD'], cwd=ROOT,
                             capture_output=True, text=True, encoding='utf-8').stdout.strip(),
    'items': [
        {
            'id': 'R1',
            'review_claim': ('the reports treat W5/W7 ("the reading is invariant along the orbit, hence descends '
                             'to the quotient") as a necessary condition for (9-1)'),
            'verdict': 'WRONG, withdrawn',
            'why': ('existence of a choice making the two maps equal does not force the reading to be invariant '
                    'along the whole family; the regression file proves the gap on a two-element family'),
            'changes': [
                {'path': assessment, 'section': '3, item 1',
                 'change': ('rewritten: existence of a choice is a strictly weaker statement than invariance; W5/W7 '
                            'is a different, stronger family condition, not a prerequisite'),
                 'sha256': sha(ROOT / assessment)},
                {'path': path_doc, 'section': 'the W5/W7 row and the two lines after it',
                 'change': 'same correction, with the regression theorem cited by name',
                 'sha256': sha(ROOT / path_doc)},
            ],
            'evidence': [
                {'path': 'research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean',
                 'declaration': 'existence_does_not_force_invariance'},
            ],
            'status': 'FIXED',
        },
        {
            'id': 'R2',
            'review_claim': ('W9 and W10 silence the unused-variable linter with '
                             '`set_option linter.unusedVariables false in` instead of removing the unused '
                             'hypotheses (W9 `hMN`, W10 `hx`)'),
            'verdict': 'CORRECT, fixed at the source',
            'changes': [
                {'path': 'candidates/core-transport/ExponentUniqueness.lean',
                 'original_commit': 'ba78ff1', 'sha256': sha(ROOT / 'candidates/core-transport/ExponentUniqueness.lean'),
                 'change': ('set_option removed; `not_determined_by_torsion_probe` no longer carries the unused '
                            '`hMN`; new `torsion_probe_witness` states the two exponents 0 and 1 explicitly')},
                {'path': 'candidates/core-transport/H3Synthesis.lean',
                 'original_commit': '64126ef', 'sha256': sha(ROOT / 'candidates/core-transport/H3Synthesis.lean'),
                 'change': ('set_option removed; `comparison_well_defined` no longer carries the unused probe '
                            'hypothesis, so the probe condition lives only in `exponent_unique` where it is used')},
            ],
            'verification': {
                'W9': rebuilt['W9']['gates']['cli']['diagnostics'] | {'source_sha256': sha(ROOT / 'candidates/core-transport/ExponentUniqueness.lean')},
                'W10': rebuilt['W10']['gates']['cli']['diagnostics'] | {'source_sha256': sha(ROOT / 'candidates/core-transport/H3Synthesis.lean')},
                'grep': ('set_option -> 0 matches in both files; hMN -> 0 matches in W9; the remaining hx '
                         'occurrences are used hypotheses (W9: hasSum_logTerm_localLog, localLog_pow_eq_smul; '
                         'W10: exponent_unique, zero_reading_powers_agree), and W10 `comparison_well_defined` '
                         'carries no probe hypothesis at all'),
            },
            'status': 'FIXED',
        },
        {
            'id': 'R3',
            'review_claim': ('the W11 editor evidence is an empty Problems panel, which does not show that the '
                             'file was checked or that its own axiom report was ever displayed'),
            'verdict': 'CORRECT, and the stronger reading was not reached',
            'changes': [
                {'path': 'handoffs/core-backward-2026-10-23/W11/capture-axiom-report.ps1',
                 'change': ('instrument rewritten across four revisions: TreeItem scope, filter to the file, panel '
                            'opened before elaboration, restart-file fallback; refuses to pass on a partial reading')},
                {'path': 'handoffs/core-backward-2026-10-23/W11/editor/README.md',
                 'change': 'the four sessions, their exit codes and what the editor plane does and does not certify'},
                {'path': 'handoffs/core-backward-2026-10-23/W11/delivery.json',
                 'change': ('editor gate lowered: errors/warnings are "not attested by the editor", status '
                            'CLI_CHECKED_EDITOR_PENDING, editor_run false')},
            ],
            'evidence': {
                'capture_json': 'handoffs/core-backward-2026-10-23/W11/editor/capture-axiom-report.json',
                'capture_sha256': sha(BASE / 'W11/editor/capture-axiom-report.json'),
                'tree': 'handoffs/core-backward-2026-10-23/W11/editor/vscode-observation-axioms.txt',
                'tree_sha256': sha(BASE / 'W11/editor/vscode-observation-axioms.txt'),
                'axiom_rows_for_the_file': capture['axiomRows'],
                'error_or_warning_rows': capture['errorOrWarningRows'],
                'no_results_banner': capture['noResultsBannerSeen'],
                'workspace_problems_reported_by_the_panel': 47,
            },
            'status': 'PARTIAL (label lowered, evidence not obtained)',
            'unresolved': ('the editor plane never elaborated EtaComparison.lean in four sessions, so the file\'s '
                           'own `#print axioms` report was not displayed there; the axiom footprint rests on the '
                           'CLI plane only (43 declarations, 43 reports)'),
        },
        {
            'id': 'R4',
            'review_claim': 'three documentation errors',
            'verdict': 'CORRECT, fixed',
            'changes': [
                {'path': 'research/core-backward-2026-10-23/lana-report-assessment.md',
                 'change': '54 -> 50 page markers, counted from the retrieved text, not estimated'},
                {'path': 'research/core-backward-2026-10-23/lana-report-assessment.md',
                 'change': ('"同一对象两种呈现" replaced by "同一兼容性目标的模型化接口，忠实性尚未证明": the toy and '
                            'the source reduction are not two presentations of one object')},
                {'path': 'research/core-backward-2026-10-23/lana-report-assessment.md',
                 'change': ('the repository comparison now lists 6 new Lean files '
                            '(Reconstruction/Cusp/{BelyiSpec,Cor37c,SurfaceGeom,SurfacePi1}.lean, '
                            'Reconstruction/Thm19/{CuspPrincipal,NFKummer}.lean) and 5 modified Lean files '
                            '(Iut.lean, Iut/Anabelian/Tempered.lean, Iut/Anabelian/TemperedAndre.lean, '
                            'Iut/Reconstruction/Cusp/Belyi.lean, Iut/Reconstruction/Cusp/Elliptic.lean) '
                            'alongside the non-Lean changes')},
            ],
            'status': 'FIXED',
        },
    ],
    'editor_evidence_sweep': {
        'what_was_counted': 'occurrences of "depends on axioms" in each task\'s editor tree dump',
        'counts': editor_sweep,
        'reading': [
            'W8, W9 and W11 have 0: their editor trees contain no axiom row at all, so for those three the '
            'EDITOR_CHECKED label was never supported by the evidence file, and all three are lowered to '
            'CLI_CHECKED_EDITOR_PENDING in this round',
            'the other tasks have 11-13 rows, but those rows name files of other tasks that shared the window '
            '(the W10 tree, for instance, carries ExponentUniqueness rows, not H3Synthesis ones), so for them '
            'the panel proves that the channel worked in that window, not that their own file was reported',
            'consequence for the reviewer: EDITOR_CHECKED in this batch should be read as "the editor plane '
            'showed no error or warning row for the window", and the per-file axiom footprint should be taken '
            'from the CLI plane, where it is produced and hashed',
        ],
        'downgraded_in_this_round': ['W8', 'W9', 'W11'],
    },
    'commands': [
        {'cmd': 'lake build (candidates/core-transport) with -DwarningAsError=true',
         'result': 'exit 0, stderr 0 bytes, for both R2 files; declaration counts 19 (W9) and 21 (W10), '
                   'errors 0, warnings 0'},
        {'cmd': 'cdsa/checks/check_lean_candidate.py --build-lib --axiom-source --require-all-axioms',
         'result': 'PASS after the R2 edits; check.json refreshed for W9 and W10'},
        {'cmd': 'py -3 handoffs/core-backward-2026-10-23/apply_r2_deliveries.py',
         'result': 'W9/W10 delivery records updated with review_fixes; outputs later rebuilt by this script '
                   'because the applier duplicated an entry with an absolute path'},
        {'cmd': 'powershell -File W11/capture-axiom-report.ps1 -File EtaComparison.lean -WaitSeconds 240',
         'result': 'exit 6: filter typed, panel holds 0 rows for the file, "no results under filter" banner, '
                   '47 workspace problems belonging to other files'},
    ],
    'unresolved': [
        'the W11 editor plane is PENDING, not checked: four capture sessions, documented in W11/editor/README.md',
        'the editor gate of every other task in this batch is asserted over the window, not over the task file '
        '(see editor_evidence_sweep); relabelling all of them is a larger decision than this fix round should take',
    ],
    'core_gap': 'OPEN',
}


def verify(obj):
    """Every hash in the record must match the file on disk."""
    bad = []

    def walk(node):
        if isinstance(node, dict):
            if 'path' in node and 'sha256' in node and isinstance(node['sha256'], str) and len(node['sha256']) == 64:
                p = ROOT / node['path']
                if not p.exists() or sha(p) != node['sha256']:
                    bad.append(node['path'])
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(obj)
    return bad


bad = verify(record)
if bad:
    raise SystemExit('hash mismatch: ' + ', '.join(bad))

dump(BASE / 'fix-delivery.json', record)
print('fix-delivery.json written')
print('  R1', sha(ROOT / assessment)[:16], sha(ROOT / path_doc)[:16])
print('  R2', sha(ROOT / 'candidates/core-transport/ExponentUniqueness.lean')[:16],
      sha(ROOT / 'candidates/core-transport/H3Synthesis.lean')[:16])
print('  R3 axiomRows', capture['axiomRows'], 'errorRows', capture['errorOrWarningRows'])
print('  sweep', json.dumps(editor_sweep))
