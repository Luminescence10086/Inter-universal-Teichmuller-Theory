"""Manual replay of test_hull_tool.py's emission test, using a fixed-name directory.

Reason: the DSH workspace-write sandbox denies file creation inside directories
created by tempfile.mkdtemp (WinError 5), so the shipped unittest's emission case
errors for an environment reason.  This script exercises the same code paths
(emit -> PROPOSED, duplicate-emit rejection, invalid_artifacts -> INVALID_INPUT)
in a fixed-name directory instead.  It changes no candidate source.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))

import hull_tool as tool

checks = {}


def main():
    runs = Path('runs')
    base = runs / 'manual-emission'
    for sub in ('valid', 'bad'):
        target = base / sub
        if target.exists():
            for item in sorted(target.rglob('*'), reverse=True):
                item.unlink() if item.is_file() else item.rmdir()
            target.rmdir()
    (base / 'valid').parent.mkdir(parents=True, exist_ok=True)
    base.mkdir(parents=True, exist_ok=True)
    source = base / 'input.json'
    if source.exists():
        source.unlink()

    source.write_text('{"schema":1,"p":5,"N":3,"thresholds":[0,2,3],'
                      '"permutations":[[1,2,0]],"require_enlargement":false}')
    manifest = tool.emit(source, base / 'valid')
    checks['status'] = manifest['status']
    checks['hull_thresholds'] = manifest['result']['hull_thresholds']
    checks['has_enlargement_theorem'] = 'HullToolCertificate.enlargement' in manifest['theorem_names']

    try:
        tool.emit(source, base / 'valid')
        checks['duplicate_emit'] = 'NO ERROR (bad)'
    except tool.InputError:
        checks['duplicate_emit'] = 'InputError'

    source.write_text('{"schema":1,"schema":1}')
    try:
        tool.emit(source, base / 'bad')
        checks['duplicate_key_emit'] = 'NO ERROR (bad)'
    except (tool.InputError, ValueError):
        checks['duplicate_key_emit'] = 'rejected'

    rejected = tool.invalid_artifacts(source, base / 'bad', 'duplicate key')
    checks['invalid_status'] = rejected['status']
    checks['invalid_theorem_names'] = rejected['theorem_names']
    checks['invalid_files'] = all((base / 'bad' / n).is_file()
                                  for n in ('request.json', 'result.json',
                                            'certificate.lean', 'manifest.json'))

    ok = (checks['status'] == 'PROPOSED'
          and checks['hull_thresholds'] == [3, 0, 2]
          and checks['has_enlargement_theorem'] is False
          and checks['duplicate_emit'] == 'InputError'
          and checks['duplicate_key_emit'] == 'rejected'
          and checks['invalid_status'] == 'INVALID_INPUT'
          and checks['invalid_theorem_names'] == []
          and checks['invalid_files'] is True)
    print(json.dumps({'checks': checks, 'all_ok': ok}, ensure_ascii=True))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
