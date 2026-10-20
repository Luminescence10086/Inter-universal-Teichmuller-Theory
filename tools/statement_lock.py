"""Legacy printed-statement change ledger, not a lock on mathematical meaning.

Each project's verifier pins source-file hashes in `verification/checked-inputs.json`.
That catches source edits, but it cannot tell "this file changed" from "this theorem's
statement changed". A later round could weaken or strengthen a statement, re-run a
verifier, refresh the file hashes, and every downstream claim would then be justified
by a different proposition while the evidence still looks green.

This tool pins, for every theorem of every project, the hash of its **normalised
elaborated statement** together with its axiom set. Default mode refuses:

  * a changed printed statement (possibly only an equivalent rewrite),
  * a removed theorem    (a name that the ledgers still rely on),
  * a changed axiom set  (a theorem that quietly gained a nonstandard axiom).

Additions are reported but pass, because new theorems are how the work grows.
`--update --note "..."` re-locks deliberately and appends a history record, so the
reasons stay auditable instead of living in someone's memory.

Definition bodies are not checked by this legacy ledger. The integrated
`tools/semantic_lock.py` additionally fingerprints project definitions and modules,
keeps qualified names, and requires complete source/runtime freshness.

Reuse: export parsing, staleness detection and statement normalisation come from
`tools/bridge.py`, so the two auditors cannot drift apart.

Usage:
  python tools/statement_lock.py                      # check (default, non-zero on drift)
  python tools/statement_lock.py --update --note "round 7: weighted ledger"
"""
from __future__ import annotations
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bridge import (  # noqa: E402  (same-directory import is intentional)
    PROJECTS,
    ROOT,
    load_json,
    norm_statement,
    project_constants,
)

LOCK = ROOT / 'bridges' / 'statement-lock.json'


def fingerprint(row, prefixes):
    return {
        'sha256': hashlib.sha256(norm_statement(row['statement'], prefixes).encode('utf-8')).hexdigest(),
        'module': row['module'],
        'axioms': sorted(row['axioms']),
    }


def collect(prefixes):
    state = {}
    for project in PROJECTS:
        rows_by_id, _ = project_constants(project)
        theorems = {
            name: fingerprint(row, prefixes)
            for name, row in rows_by_id.items()
            if row['kind'] == 'theorem'
        }
        state[project] = theorems
    return state


def diff(locked, current):
    changed, removed, added = [], [], []
    for project, theorems in locked.get('projects', {}).items():
        live = current.get(project, {})
        for name, old in theorems.items():
            if name not in live:
                removed.append(f'{project}:{name}')
                continue
            new = live[name]
            if new['sha256'] != old['sha256']:
                changed.append(f'{project}:{name} (statement)')
            elif new['axioms'] != old['axioms']:
                changed.append(f'{project}:{name} (axioms {old["axioms"]} -> {new["axioms"]})')
            elif new['module'] != old['module']:
                changed.append(f'{project}:{name} (module)')
    for project, theorems in current.items():
        for name in theorems:
            if name not in locked.get('projects', {}).get(project, {}):
                added.append(f'{project}:{name}')
    return sorted(changed), sorted(removed), sorted(added)


def main(argv):
    update = '--update' in argv
    note = ''
    if '--note' in argv:
        note = argv[argv.index('--note') + 1]

    spec = load_json(ROOT / 'bridges' / 'contracts.json')
    prefixes = spec['normalisation']['strip_prefixes']
    current = collect(prefixes)
    total = sum(len(v) for v in current.values())

    if update:
        locked = load_json(LOCK) if LOCK.exists() else {'schema': 1, 'projects': {}, 'history': []}
        changed, removed, added = diff(locked, current)
        locked['projects'] = current
        locked.setdefault('history', []).append({
            'utc': datetime.now(timezone.utc).isoformat(),
            'note': note,
            'theorems': total,
            'changed': changed,
            'removed': removed,
            'added': added,
        })
        locked['generated_utc'] = datetime.now(timezone.utc).isoformat()
        locked['schema'] = 1
        locked['scope'] = (
            'Normalised elaborated statements plus axiom sets of every theorem in the three '
            'verification projects. Printed text fingerprints only; not meaning or truth.'
        )
        LOCK.write_text(json.dumps(locked, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        print(f'statement lock updated: {total} theorems '
              f'({len(changed)} changed, {len(removed)} removed, {len(added)} added)')
        for item in changed:
            print('  changed', item)
        for item in removed:
            print('  removed', item)
        return 0

    if not LOCK.exists():
        print('statement lock missing; run with --update --note "..." first')
        return 2
    locked = load_json(LOCK)
    changed, removed, added = diff(locked, current)
    print(f'statement lock: {total} theorems checked '
          f'({len(changed)} changed, {len(removed)} removed, {len(added)} added)')
    for item in changed:
        print('  FAIL changed', item)
    for item in removed:
        print('  FAIL removed', item)
    for item in added:
        print('  new (not yet locked)', item)
    if changed or removed:
        print('printed statement drift detected: review before changing the baseline')
        return 1
    print('no statement or axiom drift')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
