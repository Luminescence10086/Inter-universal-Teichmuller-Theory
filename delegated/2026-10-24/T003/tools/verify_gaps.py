"""T003: re-run every NEGATIVE search that backs api-map.json `gaps`.

Read-only. Writes a machine-comparable report: for each gap id, the exact terms and
the hit counts. A gap's claim is only believable if these counts stay 0 (or stay
confined to the file that the claim says they are confined to).

Usage:
    python tools/verify_gaps.py <mathlib_root> <out.json>
"""
import io
import json
import os
import re
import sys

GAP_QUERIES = [
    {
        'id': 'G1',
        'claim': 'no PowerSeries.comp composition operation',
        'patterns': [r'^def comp', r'^theorem comp_assoc', r'PowerSeries\.comp\b'],
        'scope_dirs': ['Mathlib/RingTheory/PowerSeries', 'Mathlib/RingTheory/MvPowerSeries',
                       'Mathlib/RingTheory/FormalGroup'],
        'expect_zero': True,
        'contrast': {
            'why': 'Polynomial.comp does exist; the asymmetry is the citable fact',
            'path': 'Mathlib/Algebra/Polynomial/Eval/Defs.lean',
            'pattern': r'^def comp \(p q : R\[X\]\)',
        },
    },
    {
        'id': 'G2',
        'claim': 'no SubstEquiv / substitution group packaging',
        'patterns': [r'substEquiv', r'SubstEquiv', r'IsSubstEquiv', r'substMonoid'],
        'scope_dirs': ['Mathlib'],
        'expect_zero': True,
    },
    {
        'id': 'G3',
        'claim': 'no Rˣ ≃* (R⟦X⟧)ˣ unit isomorphism; only IsUnit-level bridge',
        'patterns': [r'def unitsEquiv', r'≃\* .*⟦X⟧ˣ', r'MvPowerSeries\.unitsEquiv'],
        'scope_dirs': ['Mathlib/RingTheory/PowerSeries'],
        'expect_zero': True,
        'contrast': {
            'why': 'the actual bridges that DO exist',
            'path': 'Mathlib/RingTheory/PowerSeries/Inverse.lean',
            'pattern': r'^theorem isUnit_iff_constantCoeff',
        },
    },
    {
        'id': 'G4',
        'claim': 'no Tate/theta/q-expansion power-series layer',
        'patterns': [r'TateParameter', r'thetaFunction', r'ThetaGroup'],
        'scope_dirs': ['Mathlib'],
        'expect_zero': True,
        'contrast': {
            'why': 'qExpansion exists only in modular forms, unrelated to PowerSeries.subst',
            'path': 'Mathlib/NumberTheory/ModularForms',
            'pattern': r'qExpansion',
        },
    },
]


def walk_lean(root, subdirs):
    for sub in subdirs:
        base = os.path.join(root, sub.replace('/', os.sep))
        if not os.path.isdir(base):
            continue
        for dirpath, _, names in os.walk(base):
            for n in names:
                if n.endswith('.lean'):
                    yield os.path.join(dirpath, n)


def count_hits(root, patterns, subdirs):
    compiled = [re.compile(p) for p in patterns]
    hits = []
    for path in walk_lean(root, subdirs):
        try:
            text = io.open(path, encoding='utf-8').read()
        except (UnicodeDecodeError, OSError):
            continue
        for i, line in enumerate(text.split('\n'), 1):
            for pat in compiled:
                if pat.search(line):
                    hits.append({
                        'file': os.path.relpath(path, root).replace(os.sep, '/'),
                        'line': i,
                        'pattern': pat.pattern,
                        'text': line.strip()[:200],
                    })
                    break
    return hits


def main():
    root, out_path = sys.argv[1], sys.argv[2]
    report = {'mathlib_root': root, 'queries': []}
    failures = []

    for q in GAP_QUERIES:
        hits = count_hits(root, q['patterns'], q['scope_dirs'])
        ok = (len(hits) == 0) if q['expect_zero'] else (len(hits) > 0)
        row = {
            'id': q['id'],
            'claim': q['claim'],
            'patterns': q['patterns'],
            'scope_dirs': q['scope_dirs'],
            'hit_count': len(hits),
            'hits': hits[:20],
            'expect_zero': q['expect_zero'],
            'verdict': 'CONFIRMED' if ok else 'CONTRADICTED',
        }
        if 'contrast' in q:
            c = q['contrast']
            cp = os.path.join(root, c['path'].replace('/', os.sep))
            if os.path.isdir(cp):
                chits = count_hits(root, [c['pattern']], [c['path']])
            elif os.path.isfile(cp):
                text = io.open(cp, encoding='utf-8').read()
                chits = [{'file': c['path'], 'line': i, 'text': ln.strip()[:200]}
                         for i, ln in enumerate(text.split('\n'), 1)
                         if re.search(c['pattern'], ln)]
            else:
                chits = []
            row['contrast'] = {'why': c['why'], 'path': c['path'],
                               'pattern': c['pattern'], 'hit_count': len(chits),
                               'hits': chits[:5]}
            if not chits:
                row['contrast']['verdict'] = 'MISSING_CONTRAST'
        if row['verdict'] != 'CONFIRMED':
            failures.append(q['id'])
        report['queries'].append(row)

    report['failures'] = failures
    report['result'] = 'ALL_GAPS_CONFIRMED' if not failures else 'GAP_CONTRADICTIONS_PRESENT'
    with io.open(out_path, 'w', encoding='utf-8') as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)
        fh.write('\n')
    print('result=%s failures=%s' % (report['result'], failures or 'none'))
    return 0 if not failures else 3


if __name__ == '__main__':
    raise SystemExit(main())
