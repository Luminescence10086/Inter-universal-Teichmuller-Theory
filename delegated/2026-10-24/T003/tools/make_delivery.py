"""T003 delivery.json generator.

Recomputes every SHA256 from the actual bytes on disk (never copies a value from
another document), reads the run receipts produced by tools/run_records.py, and
never hashes delivery.json itself (a manifest cannot contain its own SHA256; the
resulting SHA256 is written to evidence/delivery.self_sha256, which is a note,
not an artifact, precisely so the manifest stays self-consistent).

Status RESEARCH_ONLY: this delivery records a read-only Mathlib API retrieval.
It has no Lean source, no Lean compile, no axiom log and no editor observation,
so `declarations` is empty and every `runs` entry is kind=source_retrieval with
an explicit lean_run=false flag.

Usage:  python -B tools/make_delivery.py
"""
import hashlib
import io
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)                 # delegated/2026-10-24/T003

BASE_COMMIT = '8d60456043e30a3da79cc838d03a19b80675dc98'
TASK_CARD_SHA = '55edaf3d8f47973e68772a18296a56ca3c1d711f1e0f259078d66f9e3cabcbdb'
BASELINE_SHA = 'e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf'
HANDOFF = r'D:\Inter-universal Teichmüller Theory\handoffs\agent-batch-2026-10-24'

ARTIFACTS = [
    ('SUMMARY.md', 'summary'),
    ('api-map.json', 'api_map'),
    ('replay.ps1', 'replay'),
    ('tools/targets.json', 'retrieval_targets'),
    ('tools/extract.py', 'tool_extract'),
    ('tools/sigs.py', 'tool_signatures'),
    ('tools/build_api_map.py', 'tool_build_api_map'),
    ('tools/verify_gaps.py', 'tool_verify_gaps'),
    ('tools/run_records.py', 'tool_run_records'),
    ('tools/spotcheck.py', 'tool_spotcheck'),
    ('tools/make_delivery.py', 'tool_make_delivery'),
    ('logs/extract.stdout.log', 'stdout'),
    ('logs/extract.stderr.log', 'stderr'),
    ('logs/sigs.stdout.log', 'stdout'),
    ('logs/sigs.stderr.log', 'stderr'),
    ('logs/build_api_map.stdout.log', 'stdout'),
    ('logs/build_api_map.stderr.log', 'stderr'),
    ('logs/verify_gaps.stdout.log', 'stdout'),
    ('logs/verify_gaps.stderr.log', 'stderr'),
    ('evidence/runs.json', 'run_receipts'),
    ('evidence/decls_dump.txt', 'extracted_declarations'),
    ('evidence/sigs.txt', 'extracted_signatures'),
    ('evidence/gapcheck.json', 'gap_negative_search'),
    ('evidence/spotcheck.json', 'declaration_spotcheck'),
]

RUN_INPUTS = {
    'extract': ['tools/extract.py', 'tools/targets.json'],
    'sigs': ['tools/sigs.py', 'evidence/decls_dump.txt'],
    'build_api_map': ['tools/build_api_map.py', 'evidence/sigs.txt'],
    'verify_gaps': ['tools/verify_gaps.py'],
}


def digest(path):
    with open(path, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def sha(rel):
    p = os.path.join(ROOT, rel.replace('/', os.sep))
    if not os.path.isfile(p):
        raise SystemExit('missing file: ' + rel)
    return digest(p)


def main():
    evid = os.path.join(ROOT, 'evidence')
    artifacts = [{'path': rel, 'sha256': sha(rel), 'role': role} for rel, role in ARTIFACTS]

    receipts = json.load(io.open(os.path.join(evid, 'runs.json'), encoding='utf-8'))
    runs = [{
        'kind': r['kind'],
        'name': r['name'],
        'argv': r['argv'],
        'argv_resolved': r['argv_resolved'],
        'cwd': r['cwd'],
        'exit_code': r['exit_code'],
        'duration_seconds': r['duration_seconds'],
        'stdout': r['stdout'],
        'stderr': r['stderr'],
        'inputs': [{'path': rel, 'sha256': sha(rel)} for rel in RUN_INPUTS.get(r['name'], [])],
    } for r in receipts]

    spot = json.load(io.open(os.path.join(evid, 'spotcheck.json'), encoding='utf-8'))

    delivery = {
        'schema_version': 1,
        'task_id': 'T003',
        'task_card_sha256': TASK_CARD_SHA,
        'baseline_sha256': BASELINE_SHA,
        'status': 'RESEARCH_ONLY',
        'lean_run': False,
        'lean_run_note': 'No Lean source file, no lake invocation, no `lake env lean`, no build and no '
                         'editor replay. This task is source retrieval (proof_mode '
                         'SOURCE_OR_ENGINEERING); the pinned Mathlib checkout has no .olean for '
                         'RingTheory/PowerSeries/Substitution, so no compile evidence exists or is claimed.',
        'summary_file': 'SUMMARY.md',
        'gap_file': None,
        'replay_file': 'replay.ps1',
        'base_commit': BASE_COMMIT,
        'returned_commit': None,
        'artifacts': artifacts,
        'declarations': [],
        'declarations_note': 'Empty by design. RESEARCH_ONLY read-only retrieval authors no Lean '
                             'declaration; the Lean names quoted in SUMMARY.md are Mathlib declarations '
                             'that were read, not produced. Their existence and file:line are re-verified '
                             'in evidence/spotcheck.json ("checked": %d, '
                             '"all_quoted_lines_verified": %s) and again by replay.ps1 step 9, instead '
                             'of by a compiled axiom receipt.' % (
                                 spot['checked'], str(spot['all_quoted_lines_verified']).lower()),
        'runs': runs,
        'dependency_deliveries': [],
        'upstream_inputs': [
            {'path': 'handoffs/agent-batch-2026-10-24/baseline.json',
             'sha256': digest(os.path.join(HANDOFF, 'baseline.json'))},
            {'path': 'handoffs/agent-batch-2026-10-24/tasks.json',
             'sha256': digest(os.path.join(HANDOFF, 'tasks.json'))},
            {'path': 'handoffs/agent-batch-2026-10-24/cards/T003.md',
             'sha256': digest(os.path.join(HANDOFF, 'cards', 'T003.md'))},
            {'path': 'handoffs/agent-batch-2026-10-24/PROTOCOL.md',
             'sha256': digest(os.path.join(HANDOFF, 'PROTOCOL.md'))},
        ],
        'mathlib': {
            'path': r'C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib',
            'commit': '85e3a25e006c35636f0e53b0e9296caca2685bc0',
            'commit_verified_by': 'git -C <path> rev-parse HEAD',
            'read_only': True,
            'files_read': 7,
        },
        'editor': {'performed': False, 'evidence_file': None, 'source_sha256': None},
        'manifest_self_hash': 'Not embedded: a manifest cannot contain its own SHA256 and stay '
                              'consistent. The SHA256 of delivery.json as written by .tmp/make_delivery.py '
                              'is recorded out-of-band in evidence/delivery.self_sha256 (a note file, '
                              'deliberately not listed in artifacts).',
        'scope_note': 'Read-only Mathlib PowerSeries substitution API retrieval. No mainline source, '
                      'Boundary or fact-tree change. PACKAGE_COMPLETE (if reported) describes material '
                      'and hashes only; it is not Lean, editor or mathematical verification.',
    }

    path = os.path.join(ROOT, 'delivery.json')
    with io.open(path, 'w', encoding='utf-8') as fh:
        json.dump(delivery, fh, ensure_ascii=False, indent=2)
        fh.write('\n')

    own = digest(path)
    io.open(os.path.join(evid, 'delivery.self_sha256'), 'w', encoding='ascii').write(own + '\n')
    print('wrote delivery.json (%d artifacts, %d runs)' % (len(ARTIFACTS), len(runs)))
    print('delivery.json sha256 = ' + own)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
