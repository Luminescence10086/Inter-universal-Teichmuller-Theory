"""Compute, for each theorem in a Lean file, the line just after its proof ends.

The Infoview's Tactic state section reports the goal list at the cursor, so the cursor must sit
after the last tactic of the block. Getting this wrong is not harmless: the first version treated
a section comment `/-! ... -/` that follows a declaration as part of that declaration and pushed
the cursor past it, so five declarations read empty.

So: mark every line that lies inside any comment region (`/-- … -/`, `/-! … -/`, `/- … -/`,
including nested), then take the last non-blank, non-comment line before the next declaration.
"""
import re
import sys
from pathlib import Path

DECL = re.compile(r'^(theorem|lemma|def|structure|instance)\s+([^\s:({[]+)')


def comment_mask(lines: list[str]) -> list[bool]:
    mask, depth = [], 0
    for line in lines:
        inside = depth > 0
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith('--', i):
                mask.append(True)
                inside = True
                break
            if line.startswith('/-', i):
                depth += 1
                inside = True
                i += 2
                continue
            if depth > 0 and line.startswith('-/', i):
                depth -= 1
                i += 2
                continue
            i += 1
        mask.append(inside or depth > 0)
    return mask


def targets(path: Path) -> list[tuple[str, int]]:
    lines = path.read_text(encoding='utf-8').splitlines()
    mask = comment_mask(lines)
    starts = [(i, m.group(1), m.group(2)) for i, line in enumerate(lines)
              for m in [DECL.match(line)] if m and not mask[i]]
    out = []
    for k, (i, kind, name) in enumerate(starts):
        nxt = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        end = nxt - 1
        while end > i and (lines[end].strip() == '' or mask[end]):
            end -= 1
        if kind in ('theorem', 'lemma', 'instance'):
            out.append((name, end + 2))
    return out


for p in sys.argv[1:]:
    path = Path(p)
    print(f'### {path.name}')
    for name, line in targets(path):
        print(f'{name}:{line}')
