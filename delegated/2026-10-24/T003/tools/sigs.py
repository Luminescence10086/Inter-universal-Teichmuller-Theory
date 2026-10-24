"""T003: split a verbatim declaration block into (signature, proof-body) parts.

The dump produced by extract.py contains whole declaration blocks, proof body included.
This tool cuts each block at the first top-level terminator (`:=`, ` by`, ` where`,
or an equation-style `|` line) so the result is exactly the declared signature as
written in the Mathlib source. No reformatting of the signature itself.
"""
import io
import re
import sys

TERMINATORS = (
    re.compile(r'^by$'),
    re.compile(r'^where$'),
    re.compile(r'^\|'),
)
DEPTH_OPEN = '([{⟨⦃'
DEPTH_CLOSE = ')]}⟩⦄'


def _find_terminator(ln, depth):
    """Return (cut_index, new_depth) for the first top-level terminator in `ln`."""
    i = 0
    while i < len(ln):
        ch = ln[i]
        if ch in DEPTH_OPEN:
            depth += 1
        elif ch in DEPTH_CLOSE:
            depth -= 1
        elif depth <= 0 and ln.startswith(':=', i):
            return i, depth
        i += 1
    return -1, depth


def split_block(block):
    lines = block.split('\n')
    out = []
    depth = 0
    for ln in lines:
        stripped = ln.strip()
        if any(t.match(stripped) for t in TERMINATORS):
            break
        cut, depth = _find_terminator(ln, depth)
        if cut >= 0:
            head = ln[:cut]
            if head.strip():
                out.append(head.rstrip())
            break
        if re.search(r'\bby\b\s*$', stripped):
            head = re.sub(r'\s*by\s*$', '', ln)
            if head.strip():
                out.append(head.rstrip())
            break
        if re.search(r'\bwhere\s*$', stripped):
            head = re.sub(r'\s*where\s*$', '', ln)
            if head.strip():
                out.append(head.rstrip())
            break
        out.append(ln.rstrip())
    return '\n'.join(l for l in out if l.strip())


def main():
    src, dst = sys.argv[1], sys.argv[2]
    text = io.open(src, encoding='utf-8').read()
    lines = text.split('\n')
    # Track the enclosing "FILE:" banner so each entry carries its true relative path.
    buf = []
    current_file = ''
    cur_name = None
    cur_line = None
    body = []

    def flush():
        if cur_name is not None:
            buf.append('### %s  [%s:%s]' % (cur_name, current_file, cur_line))
            buf.append(split_block('\n'.join(body)))
            buf.append('')

    for ln in lines:
        if ln.startswith('FILE: '):
            flush()
            cur_name = None
            body = []
            current_file = ln[len('FILE: '):].replace('\\', '/').split('mathlib/')[-1]
            continue
        if ln.startswith('=' * 10):
            continue
        m = re.match(r'^--- (.+?)\s+\[(.+?):(\d+)\] ---$', ln)
        if m:
            flush()
            cur_name, cur_line = m.group(1).strip(), m.group(3)
            body = []
            continue
        if ln.startswith('--- ') and 'NOT FOUND' in ln:
            flush()
            cur_name = None
            body = []
            continue
        if cur_name is not None:
            body.append(ln)
    flush()
    io.open(dst, 'w', encoding='utf-8').write('\n'.join(buf))
    print('OK ' + dst)


if __name__ == '__main__':
    main()
