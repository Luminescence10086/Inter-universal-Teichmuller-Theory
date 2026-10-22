"""Cross-check driver: the CDS-A node that re-derives both candidates from scratch.

`check_lean_candidate.py` proves what one compiler run said. This driver is deliberately a
different process with different flags, so a single corrupted artifact cannot satisfy both:

  1  re-run the compiler for each candidate in strict mode (every theorem must carry an
     axiom report), independent of whatever the first pass recorded;
  2  run the claim-consistency audit (README vs source vs artifact) for each candidate, so
     a README that says more than the build shows is caught here;
  3  scan both sources for the repository's one forbidden identification: describing the
     Q_p-linear automorphism family A(k) as elements of `Ism`. That is finding F-01, the
     most dangerous false bridge in this audit, and it is a *prose* error, so no compiler
     can catch it.

Exit status is the gate. The printed JSON is the artifact the synthesis edge hashes.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

CHECKS = Path(__file__).resolve().parent
IS_TRAP = re.compile(r'(?i)(?:A\(k\)|automorphism)[^.\n]{0,120}\bis\w*\s+(?:an?\s+element|in)\s+'
                     r'(?:of\s+)?I?sm\b|I?sm[^.\n]{0,80}(?:contains|equals|=)\s*A\(k\)')


def run(argv: list[str], timeout: int) -> dict:
    try:
        proc = subprocess.run(argv, capture_output=True, timeout=timeout)
    except (subprocess.TimeoutExpired, OSError) as exc:
        return {'argv': argv, 'exit': None, 'error': f'{type(exc).__name__}: {exc}',
                'stdout': '', 'stderr': ''}
    return {'argv': argv, 'exit': proc.returncode,
            'stdout': proc.stdout.decode('utf-8', 'replace'),
            'stderr': proc.stderr.decode('utf-8', 'replace')}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description='independent cross-check of both candidates')
    parser.add_argument('--candidate', action='append', required=True,
                        help='name:project_dir:source_rel:axiom_source_rel')
    parser.add_argument('--json-dir', required=True, help='where the per-candidate JSON goes')
    parser.add_argument('--out', required=True, help='cross-check summary JSON')
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args(argv)

    json_dir = Path(args.json_dir)
    json_dir.mkdir(parents=True, exist_ok=True)
    problems, entries = [], []
    for spec in args.candidate:
        name, project, source, axiom_source = spec.split(':', 3)
        strict_json = json_dir / f'{name}.strict.json'
        check = run([sys.executable, str(CHECKS / 'check_lean_candidate.py'),
                     '--project', project, '--source', source,
                     '--axiom-source', axiom_source, '--build-lib', 'Candidates',
                     '--require-all-axioms', '--timeout', str(args.timeout),
                     '--json-out', str(strict_json)], args.timeout)
        entry = {'name': name, 'project': project, 'source': source,
                 'strict_check_exit': check['exit'], 'strict_json': str(strict_json)}
        if check['exit'] != 0:
            problems.append(f'{name}: strict compiler re-check failed '
                            f'({check["stderr"].strip().splitlines()[-1:]})')
        entries.append(entry)
        if not strict_json.exists():
            problems.append(f'{name}: strict check produced no JSON artifact')
            continue
        readme = Path(project) / 'README.md'
        claim = run([sys.executable, str(CHECKS / 'claim_consistency.py'),
                     '--readme', str(readme), '--lean', str(Path(project) / source),
                     '--check-json', str(strict_json), '--allow-verdict', 'CORE_PROVED',
                     '--allow-verdict', 'PARTIAL', '--allow-verdict', 'INCOMPLETE',
                     '--allow-verdict', 'INSTANCE_PROVED_UNBLOCKS',
                     '--allow-verdict', 'INSTANCE_PROVED_STRUCTURAL_ONLY',
                     '--allow-verdict', 'ALREADY_INSTANCE_USE_ONLY'], args.timeout)
        entry['claim_consistency_exit'] = claim['exit']
        if claim['exit'] != 0:
            problems.append(f'{name}: claim-consistency audit failed')
        text = (Path(project) / source).read_text(encoding='utf-8')
        traps = [{'line': line_number, 'text': line.strip()[:160]}
                 for line_number, line in enumerate(text.splitlines(), start=1)
                 if IS_TRAP.search(line)]
        entry['f01_traps'] = traps
        if traps:
            problems.append(f'{name}: {len(traps)} line(s) identify A(k) automorphisms with '
                            f'Ism (F-01)')

    summary = {'candidates': entries, 'problems': problems, 'ok': not problems}
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
    out.write_text(text, encoding='utf-8')
    print(text)
    print(f"RESULT: {'PASS' if summary['ok'] else 'FAIL'}", file=sys.stderr)
    return 0 if summary['ok'] else 1


if __name__ == '__main__':
    sys.exit(main())
