"""Conservative statement/definition change ledger; not a semantic proof.

Full freshness is required first. Names stay qualified. Kind, module, printed type,
axioms and every project definition's printed body are compared. Even equivalent
rewrites can trigger a review. External definitions are pinned by the project
environment, not expanded into this ledger. Historical statement-lock.json is kept.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from freshness import validate_project, verifier, assert_equal, digest

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {'main': ROOT, 'local': ROOT / 'local-field', 'bridge': ROOT / 'bridge'}
LOCK = ROOT / 'bridges/integrated-lock.json'


def text_hash(value):
    # Do not strip namespace names: unlike a correspondence comparison, a change
    # ledger should not identify distinct constants that happen to share a suffix.
    return hashlib.sha256(value.encode('utf-8')).hexdigest()


def definition_bodies(base):
    module = verifier(base)
    before = module.snapshot()
    program = base / 'tools/DefinitionBodies.lean'
    program_hash = digest(program)
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('lake is not on PATH')
    command = [lake, 'env', 'lean', '--json', '-DwarningAsError=true',
               'tools/DefinitionBodies.lean']
    result = subprocess.run(command, cwd=base, capture_output=True, text=True,
                            encoding='utf-8', timeout=300)
    record = {'command': command, 'exit_code': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr,
              'program_sha256': program_hash}
    (base / 'verification/definition-bodies.json').write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    if result.returncode or result.stderr:
        raise RuntimeError(f'Definition export failed: {result.stdout}\n{result.stderr}')
    rows = module.one_information(result.stdout)
    assert_equal(before, module.snapshot(), 'definition exporter inputs')
    if digest(program) != program_hash:
        raise RuntimeError('Definition export program changed during checking')
    return {row['id']: row['body'] for row in rows}


def fingerprint(row, bodies):
    result = {'kind': row['kind'], 'module': row['module'],
              'statement_sha256': text_hash(row['statement']),
              'axioms': sorted(row['axioms'])}
    if row['kind'] == 'definition':
        if row['id'] not in bodies:
            raise RuntimeError('Missing definition body: ' + row['id'])
        result['body_sha256'] = text_hash(bodies[row['id']])
    return result


def diff(old, new):
    changed = sorted(k for k in old.keys() & new.keys() if old[k] != new[k])
    return changed, sorted(old.keys() - new.keys()), sorted(new.keys() - old.keys())


def collect():
    state = {}
    for project, base in PROJECTS.items():
        rows, _ = validate_project(base, deep=True)
        bodies = definition_bodies(base)
        for name, row in rows.items():
            state[project + ':' + name] = fingerprint(row, bodies)
        # Actual runtime is rechecked after the diagnostic Lean process too.
        validate_project(base, deep=True)
    return state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--accept', action='store_true', help='record a reviewed baseline')
    parser.add_argument('--note', default='')
    args = parser.parse_args()
    if args.accept and not args.note.strip():
        parser.error('--accept requires a nonempty --note')
    current = collect()
    old = json.loads(LOCK.read_text(encoding='utf-8')) if LOCK.exists() else {'entries': {}}
    changed, removed, added = diff(old['entries'], current)
    if args.accept:
        history = old.get('history', []) + [{'utc': datetime.now(timezone.utc).isoformat(),
            'note': args.note, 'changed': changed, 'removed': removed, 'added': added}]
        LOCK.write_text(json.dumps({'schema': 2, 'scope': __doc__, 'entries': current,
            'history': history}, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'Change ledger: {len(current)} constants; changed={len(changed)}, '
          f'removed={len(removed)}, added={len(added)}; baseline_recorded={args.accept}')
    if not args.accept and (changed or removed or not LOCK.exists()):
        print('Review required: ' + ', '.join(changed + removed))
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
