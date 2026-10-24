"""T003: extract exact declaration signatures from a fixed Mathlib checkout (read-only).

Reads a JSON target list [[file, [names...]], ...] and writes a plain-text dump with
the source block of each declaration (line-joined, verbatim, no reformatting).
Never writes inside the Mathlib tree.
"""
import io
import json
import os
import re
import sys

DECL = re.compile(
    r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+|protected\s+|private\s+)*'
    r'(def|theorem|lemma|abbrev|structure|instance|alias)\s+(\S+)')
STOP = re.compile(
    r'^(?:theorem|lemma|def|abbrev|instance|structure|end|section|variable|open|'
    r'namespace|omit|include|attribute|@\[|/-|alias)\b')


def find(path, name):
    with io.open(path, encoding='utf-8') as fh:
        lines = fh.read().split('\n')
    res = []
    for i, ln in enumerate(lines):
        m = DECL.match(ln)
        if m and m.group(2) == name:
            blk = [ln]
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() == '' or STOP.match(nxt):
                    break
                blk.append(nxt)
                j += 1
            res.append((i + 1, '\n'.join(blk)))
    return res


def main():
    targets = json.load(io.open(sys.argv[1], encoding='utf-8'))
    buf = []
    for path, names in targets:
        buf.append('=' * 78)
        buf.append('FILE: ' + path)
        buf.append('=' * 78)
        for n in names:
            got = find(path, n)
            if not got:
                buf.append('--- %s : NOT FOUND by regex ---' % n)
                continue
            for lineno, blk in got:
                buf.append('--- %s  [%s:%d] ---' % (n, os.path.basename(path), lineno))
                buf.append(blk)
            buf.append('')
    with io.open(sys.argv[2], 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(buf))
    print('OK ' + sys.argv[2])


if __name__ == '__main__':
    main()
