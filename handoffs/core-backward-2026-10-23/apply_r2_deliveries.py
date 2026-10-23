"""Fold the R2 review fixes into the W9 and W10 delivery records."""
import hashlib
import io
import json
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
BASE = ROOT / 'handoffs/core-backward-2026-10-23'

FIXES = {
    'W9': dict(
        src='candidates/core-transport/ExponentUniqueness.lean',
        original_commit='ba78ff1',
        note=('R2: removed the set_option linter.unusedVariables silence; dropped the redundant '
              'hMN hypothesis from not_determined_by_torsion_probe and added torsion_probe_witness, '
              'which states the two different exponents 0 and 1 explicitly'),
        wording=('the probe is described as one whose reading is zero, not as non-torsion in the field'),
    ),
    'W10': dict(
        src='candidates/core-transport/H3Synthesis.lean',
        original_commit='64126ef',
        note=('R2: removed the set_option linter.unusedVariables silence; comparison_well_defined no '
              'longer carries the unused probe hypothesis, so the probe condition now lives only in '
              'exponent_unique, where it is actually used'),
        wording=('module docstring and the degeneracy docstrings were updated to the new signature'),
    ),
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


for task, fix in FIXES.items():
    p = BASE / task / 'delivery.json'
    d = json.load(io.open(p, encoding='utf-8'))
    src = fix['src']
    check = BASE / task / 'check.json'
    kept = [o for o in d['outputs']
            if o['path'] not in (src, str(check).replace('\\', '/'))]
    kept.insert(0, {'path': src, 'sha256': sha(ROOT / src)})
    kept.insert(1, {'path': str(check).replace('\\', '/'), 'sha256': sha(check)})
    d['outputs'] = kept
    d['gates']['cli']['source_sha256'] = sha(ROOT / src)
    d['gates']['cli']['diagnostics'] = json.load(io.open(check, encoding='utf-8'))['counts']
    d.setdefault('review_fixes', []).append({
        'round': 'R2', 'original_commit': fix['original_commit'],
        'new_source_sha256': sha(ROOT / src), 'note': fix['note'], 'wording': fix['wording']})
    p.write_text(json.dumps(d, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(task, 'updated:', sha(ROOT / src)[:16], d['gates']['cli']['diagnostics'])
