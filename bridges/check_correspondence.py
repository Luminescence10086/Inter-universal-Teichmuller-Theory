"""Verify the semantic-correspondence ledger without regenerating it.

Generation and verification are separate roles: this script never writes the ledger, it
only checks claims the ledger makes about itself. Exit 0 only if every check passes.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def main():
    problems = []
    ledger_path = ROOT / 'bridges/correspondence.json'
    if not ledger_path.exists():
        print('FAIL: bridges/correspondence.json missing')
        return 1
    ledger = load(ledger_path)

    known = set()
    for rel in ('bridge/verification/project-constants.json',
                'verification/project-constants.json',
                'local-field/verification/project-constants.json'):
        path = ROOT / rel
        if not path.exists():
            problems.append(f'export missing: {rel}')
            continue
        for row in load(path):
            if row.get('kind') == 'theorem':
                known.add(row['id'])

    if not known:
        problems.append('no exported theorems found; cannot validate anchors')

    for entry in ledger.get('entries', []):
        missing = [tid for tid in entry.get('formal', []) if tid not in known]
        if missing:
            problems.append(f'{entry.get("id")}: anchors not exported: {missing}')
        if entry.get('anchors_missing'):
            problems.append(f'{entry.get("id")}: ledger itself records missing anchors')
        if entry.get('evidence_tier') not in ('E1', 'E2', 'E3', 'E4'):
            problems.append(f'{entry.get("id")}: evidence tier missing or invalid')
        for field in ('proves', 'gap', 'falsifier'):
            if not str(entry.get(field, '')).strip():
                problems.append(f'{entry.get("id")}: {field} is empty')
        if not entry.get('obligation', '').startswith('RI-0'):
            problems.append(f'{entry.get("id")}: obligation is not an RI id')

    if not ledger.get('forbidden_identifications'):
        problems.append('forbidden identifications section is empty')
    for item in ledger.get('forbidden_identifications', []):
        if not item.get('why') or not item.get('would_misread'):
            problems.append(f'{item.get("id")}: forbidden identification lacks why/misread list')
    if ledger.get('anchors_all_present') is not True:
        problems.append('ledger does not claim anchors_all_present')
    if ledger.get('iut_object_constructed') is not False:
        problems.append('ledger must state iut_object_constructed = false')

    for name, rel in (ledger.get('companion_evidence') or {}).items():
        if not (ROOT / rel).exists():
            problems.append(f'companion evidence missing: {name} -> {rel}')

    if problems:
        print(f'FAIL: {len(problems)} problem(s)')
        for item in problems:
            print('  -', item)
        return 1
    print(f'PASS: {len(ledger.get("entries", []))} entries, '
          f'{ledger.get("anchor_count")} exported theorems consulted, '
          f'{len(ledger.get("forbidden_identifications", []))} forbidden identifications')
    return 0


if __name__ == '__main__':
    sys.exit(main())
