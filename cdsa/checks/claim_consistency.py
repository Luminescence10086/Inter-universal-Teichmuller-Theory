"""Claim-versus-artifact consistency: the second, independent CDS-A verification node.

`check_lean_candidate.py` proves what the toolchain said. This program proves that the
candidate's own prose did not claim more than that. It is deliberately adversarial: the
repo's review doctrine is that an author's self-check must never be the evidence for its
own claim, so every assertion here is a *mismatch detector* between three artifacts that
were produced separately:

  README.md          -- what the author says
  the .lean source   -- what exists
  the checker JSON   -- what the compiler actually reported

Checks:
  1  exactly one `VERDICT:` line, drawn from the allowed vocabulary
  2  no declaration is hidden: every theorem/instance in the source is named in the README
  3  a proof-bearing verdict requires a passing checker artifact
  4  a failing checker artifact forbids a proof-bearing verdict (overclaim detector)
  5  naming Cor 3.12 / the Theta-link / Ism requires an explicit hedging token nearby
  6  the README must carry the reproduction command and the toolchain line
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROOF_VERDICTS = {'INSTANCE_PROVED_UNBLOCKS', 'INSTANCE_PROVED_STRUCTURAL_ONLY', 'CORE_PROVED',
                  'PARTIAL', 'PASS'}
HEDGES = ('not constructed', 'forbidden', 'not attempted', 'no construction', 'NOT ',
          'out of scope', 'forbidden identification')
SENSITIVE = ('Cor 3.12', 'Corollary 3.12', 'Θ-link', 'Theta-link', 'Ism', 'abc')


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description='README claims vs recorded artifacts')
    parser.add_argument('--readme', required=True)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--check-json', required=True)
    parser.add_argument('--allow-verdict', action='append', default=[])
    args = parser.parse_args(argv)

    readme_path, lean_path, json_path = (Path(args.readme), Path(args.lean),
                                         Path(args.check_json))
    problems, notes = [], []
    for path in (readme_path, lean_path, json_path):
        if not path.exists():
            print(f'MISSING: {path}')
            return 1
    readme = readme_path.read_text(encoding='utf-8')
    source = lean_path.read_text(encoding='utf-8')
    report = json.loads(json_path.read_text(encoding='utf-8-sig'))

    # 1 -- the verdict contract
    verdicts = re.findall(r'^VERDICT:\s*([A-Z_]+)\s*$', readme, re.M)
    allowed = set(args.allow_verdict) or (PROOF_VERDICTS | {'ALREADY_INSTANCE_USE_ONLY',
                                                            'INCOMPLETE'})
    if len(verdicts) != 1:
        problems.append(f'expected exactly one VERDICT line, found {len(verdicts)}')
    elif verdicts[0] not in allowed:
        problems.append(f'verdict {verdicts[0]!r} outside allowed vocabulary {sorted(allowed)}')
    verdict = verdicts[0] if len(verdicts) == 1 else None
    notes.append(f'verdict={verdict}')

    # 2 -- nothing hidden
    hidden = []
    for match in re.finditer(r'^(theorem|lemma|instance)\s+([^\s:({\[]+)', source, re.M):
        name = match.group(2)
        if name not in readme:
            hidden.append(name)
    if hidden:
        problems.append(f'declarations never mentioned in the README: {hidden}')
    notes.append(f'declarations_checked={len(re.findall(r"^(?:theorem|lemma|instance)", source, re.M))}')

    # 3 + 4 -- the artifact decides whether a proof-bearing verdict is allowed
    checker_ok = bool(report.get('ok'))
    checker_errors = int(report.get('counts', {}).get('errors', -1))
    if verdict in PROOF_VERDICTS and not checker_ok:
        problems.append(f'verdict {verdict} claims proof but checker artifact failed: '
                        f'{report.get("failures")}')
    if checker_ok and verdict == 'INCOMPLETE':
        problems.append('checker passed but the README still says INCOMPLETE (stale claim)')
    if checker_errors > 0 and verdict in PROOF_VERDICTS:
        problems.append(f'{checker_errors} error diagnostics contradict verdict {verdict}')

    # 5 -- the three dangerous names may only appear hedged
    for name in SENSITIVE:
        if name in readme:
            window = readme[max(0, readme.index(name) - 400):readme.index(name) + 400]
            if not any(hedge in window for hedge in HEDGES):
                problems.append(f'{name!r} appears without a hedging token within 400 chars')
                break

    # 6 -- reproducibility claims must be checkable
    if 'lake env lean' not in readme:
        problems.append('README does not state the `lake env lean` reproduction command')
    if 'toolchain' not in readme.lower() and 'v4.34.0' not in readme:
        problems.append('README does not state the toolchain')

    out = {'readme': str(readme_path), 'lean': str(lean_path), 'check_json': str(json_path),
           'verdict': verdict, 'checker_ok': checker_ok, 'notes': notes,
           'problems': problems, 'ok': not problems}
    print(json.dumps(out, ensure_ascii=False, indent=2, sort_keys=True))
    print(f"RESULT: {'PASS' if out['ok'] else 'FAIL'}", file=sys.stderr)
    return 0 if out['ok'] else 1


if __name__ == '__main__':
    sys.exit(main())
