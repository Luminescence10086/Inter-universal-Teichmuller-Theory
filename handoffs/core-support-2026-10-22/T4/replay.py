"""T4 replay harness: run the three frozen entries once each and record real exit codes.

Written because PowerShell's `Start-Process -PassThru` + `WaitForExit` returned no usable
`ExitCode` in this environment; the handoff forbids inventing one, so the replay is driven by
a subprocess call that reports `returncode` directly. Streams are written byte-for-byte to the
files named in the handoff's delivery schema.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

LAKE = r'C:\Users\18746\.elan\bin\lake.exe'
ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
T4 = ROOT / 'handoffs' / 'core-support-2026-10-22' / 'T4'
JOBS = [
    ('qpthree', 'candidates/core-log', 'CoreLog/QpThree.lean'),
    ('completion', 'candidates/core-transport', 'CoreTransport/Completion.lean'),
    ('axiomexports', 'candidates/core-transport', 'CoreTransport/AxiomExports.lean'),
]
SOURCES = [
    'candidates/core-log/CoreLog/QpThree.lean',
    'candidates/core-transport/CoreTransport/Completion.lean',
    'candidates/core-transport/CoreTransport/AxiomExports.lean',
    'candidates/core-transport/CoreTransport/Basic.lean',
    'candidates/core-log/PadicLogVolume/PadicLog.lean',
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = {p: sha(ROOT / p) for p in SOURCES}
    results = []
    for name, cwd, target in JOBS:
        argv = [LAKE, 'env', 'lean', '-DwarningAsError=true', target]
        out_path = T4 / f'{name}.stdout.txt'
        err_path = T4 / f'{name}.stderr.txt'
        timed_out = False
        try:
            proc = subprocess.run(argv, cwd=str(ROOT / cwd), capture_output=True, timeout=300)
            code = proc.returncode
            stdout, stderr = proc.stdout, proc.stderr
        except subprocess.TimeoutExpired:
            code, stdout, stderr, timed_out = None, b'', b'', True
        out_path.write_bytes(stdout)
        err_path.write_bytes(stderr)
        record = {
            'cwd': cwd, 'argv': ['lake', 'env', 'lean', '-DwarningAsError=true', target],
            'exit_code': code, 'timed_out': timed_out,
            'stdout': str(out_path.relative_to(ROOT)).replace('\\', '/'),
            'stderr': str(err_path.relative_to(ROOT)).replace('\\', '/'),
            'stdout_sha256': sha(out_path), 'stderr_sha256': sha(err_path),
            'stdout_bytes': len(stdout), 'stderr_bytes': len(stderr),
            'axiom_report_lines': sum(1 for line in stdout.decode('utf-8', 'replace').splitlines()
                                      if 'depends on axioms' in line
                                      or 'does not depend on any axioms' in line),
            'error_lines': sum(1 for line in (stdout + stderr).decode('utf-8', 'replace').splitlines()
                               if ': error' in line),
            'warning_lines': sum(1 for line in (stdout + stderr).decode('utf-8', 'replace').splitlines()
                                 if ': warning' in line),
        }
        results.append(record)
        print(f"{name}: exit={code} timed_out={timed_out} "
              f"stdout={len(stdout)}B stderr={len(stderr)}B "
              f"axioms={record['axiom_report_lines']} errors={record['error_lines']} "
              f"warnings={record['warning_lines']}")
    after = {p: sha(ROOT / p) for p in SOURCES}
    drift = [p for p in SOURCES if before[p] != after[p]]
    (T4 / 'replay.json').write_text(
        json.dumps({'runs': results, 'sources': before, 'sources_after': after,
                    'drift': drift}, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print('drift:', drift)
    return 0 if not drift else 1


if __name__ == '__main__':
    sys.exit(main())
