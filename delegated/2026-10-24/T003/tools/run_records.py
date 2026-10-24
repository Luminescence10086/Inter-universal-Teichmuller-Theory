"""T003: re-execute the four retrievals that built this delivery, recording
argv / cwd / exit code / wall-clock duration and full stdout+stderr per run.

Writes the durable receipts into evidence/ (tracked by git) and the throwaway
work into .tmp/ (gitignored). Reads only the pinned Mathlib checkout.
No network, no lake build, no `lake env lean`, no edit of Mathlib or the main project.

Usage:  python -B tools/run_records.py
Output: evidence/runs.json
"""
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)            # .../delegated/2026-10-24/T003
LOGS = os.path.join(ROOT, 'logs')
EVID = os.path.join(ROOT, 'evidence')
TMP = os.path.join(ROOT, '.tmp')
MATHLIB = r'C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib'

STEPS = [
    ('extract',       ['-B', 'tools/extract.py', 'tools/targets.json', 'evidence/decls_dump.txt']),
    ('sigs',          ['-B', 'tools/sigs.py', 'evidence/decls_dump.txt', 'evidence/sigs.txt']),
    ('build_api_map', ['-B', 'tools/build_api_map.py', 'evidence/sigs.txt', 'api-map.json']),
    ('verify_gaps',   ['-B', 'tools/verify_gaps.py', MATHLIB, 'evidence/gapcheck.json']),
]


def main():
    for d in (LOGS, EVID, TMP):
        os.makedirs(d, exist_ok=True)
    env = dict(os.environ)
    env['TEMP'] = TMP
    env['TMP'] = TMP
    env['PYTHONDONTWRITEBYTECODE'] = '1'

    runs = []
    for name, tail in STEPS:
        out_path = os.path.join(LOGS, name + '.stdout.log')
        err_path = os.path.join(LOGS, name + '.stderr.log')
        start = time.perf_counter()
        proc = subprocess.run([sys.executable] + tail, cwd=ROOT, env=env, capture_output=True)
        duration = round(time.perf_counter() - start, 3)
        with open(out_path, 'wb') as fh:
            fh.write(proc.stdout)
        with open(err_path, 'wb') as fh:
            fh.write(proc.stderr)
        runs.append({
            'kind': 'source_retrieval',
            'name': name,
            'argv': ['python'] + tail,
            'argv_resolved': [sys.executable] + tail,
            'cwd': ROOT,
            'exit_code': proc.returncode,
            'duration_seconds': duration,
            'stdout': 'logs/' + name + '.stdout.log',
            'stderr': 'logs/' + name + '.stderr.log',
        })
        print('%-14s exit=%d %.3fs' % (name, proc.returncode, duration))
        if proc.returncode != 0:
            sys.stderr.write(proc.stderr.decode('utf-8', 'replace'))
            print('FAILED at ' + name)
            break

    with open(os.path.join(EVID, 'runs.json'), 'w', encoding='utf-8') as fh:
        json.dump(runs, fh, ensure_ascii=False, indent=2)
        fh.write('\n')
    print('wrote evidence/runs.json (%d runs)' % len(runs))
    return 0 if len(runs) == len(STEPS) and all(r['exit_code'] == 0 for r in runs) else 1


if __name__ == '__main__':
    raise SystemExit(main())
