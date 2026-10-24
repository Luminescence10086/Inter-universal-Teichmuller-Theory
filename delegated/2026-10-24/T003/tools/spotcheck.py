"""T003 spot check: do the Lean declaration names quoted in SUMMARY.md actually
exist in the pinned Mathlib, on the file and line the summary claims?

Read-only over the Mathlib checkout. A "hit" means the exact declaration token
is present on the quoted line; the script also reports every other line in the
file carrying that token, and the raw text of the quoted line so the claim can
be judged without trusting the script.
"""
import io
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EVID = os.path.join(ROOT, 'evidence')
MATHLIB = r'C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib'
SUB = 'Mathlib/RingTheory/PowerSeries/Substitution.lean'

CHECKS = [
    ('PowerSeries.HasSubst', SUB, 40, 'abbrev HasSubst'),
    ('PowerSeries.subst', SUB, 158, 'noncomputable def subst'),
    ('PowerSeries.substAlgHom', SUB, 171, 'noncomputable def substAlgHom'),
    ("PowerSeries.HasSubst.of_constantCoeff_zero'", SUB, 67, 'theorem HasSubst.of_constantCoeff_zero'),
    ('PowerSeries.subst_comp_subst_apply', SUB, 390, 'theorem subst_comp_subst_apply'),
    ('PowerSeries.subst_substInvOfIsUnit_right', SUB, 587, 'lemma subst_substInvOfIsUnit_right'),
]


def main():
    results, ok = [], True
    for name, rel, line, token in CHECKS:
        path = os.path.join(MATHLIB, rel.replace('/', os.sep))
        lines = io.open(path, encoding='utf-8').read().split('\n')
        found = token in lines[line - 1]
        hits = [i + 1 for i, ln in enumerate(lines) if token in ln]
        results.append({
            'declaration': name,
            'file': rel,
            'quoted_line': line,
            'actual_text': lines[line - 1].rstrip(),
            'text_matches_quoted_line': found,
            'all_lines_with_token': hits,
        })
        ok = ok and found
    out = {'mathlib_root': MATHLIB, 'checked': len(results),
           'all_quoted_lines_verified': ok, 'results': results}
    os.makedirs(EVID, exist_ok=True)
    text = json.dumps(out, ensure_ascii=False, indent=2)
    io.open(os.path.join(EVID, 'spotcheck.json'), 'w', encoding='utf-8').write(text + '\n')
    print(text)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
