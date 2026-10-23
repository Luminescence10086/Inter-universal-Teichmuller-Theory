#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N02 anchor extractor (read-only).

Usage:
  py -3 extract_anchors.py hash
  py -3 extract_anchors.py show  <filekey> <start> <end>
  py -3 extract_anchors.py grep  <filekey> <regex>
  py -3 extract_anchors.py page  <filekey> <start> <end>

filekey: iut3 | lana | ss | rpt2018
Page numbers are read from the '===== PDF PAGE n =====' / '===== PAGE n ====='
markers embedded in the cached text files; ss/rpt2018 have no markers (page = '-')

This script only reads inputs and prints. It never writes.
"""
import hashlib
import re
import sys

ROOT = "D:\\Inter-universal Teichm\u00fcller Theory"
FILES = {
    "iut3": ROOT + r"\research\round2-source-cache\iut-III-official-retrieved-2026-10-16.txt",
    "lana": ROOT + r"\research\round2-source-cache\LANA-interim-report-2026-07.txt",
    "ss": ROOT + r"\reviews\core-round\external\DrAbx123--Formalization-of-Inter-universal-"
          r"Teichmuller-Theory-IUT-and-abc-conjecture\vendor\promachina\snapshots\0d52e0fd5b53"
          r"\docs\scholze-stix-why-abc-is-still-a-conjecture.md",
    "rpt2018": ROOT + r"\reviews\core-round\external\DrAbx123--Formalization-of-Inter-universal-"
               r"Teichmuller-Theory-IUT-and-abc-conjecture\papers\motizuki_corpus\text\Rpt2018.txt",
}


def read_lines(key):
    with open(FILES[key], "rb") as fh:
        raw = fh.read()
    text = raw.decode("utf-8", errors="replace")
    return text.splitlines()


def pages(lines):
    out = []
    cur = "-"
    for ln in lines:
        m = re.match(r"^===== (?:PDF )?PAGE (\d+) =====\s*$", ln.strip())
        if m:
            cur = m.group(1)
            out.append(cur)
            continue
        out.append(cur)
    return out


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main(argv):
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    if not argv or argv[0] == "hash":
        for k, p in FILES.items():
            try:
                print("%-8s %s  %s" % (k, sha256(p), p))
            except OSError as exc:
                print("%-8s UNRESOLVED %s (%s)" % (k, p, exc))
        return 0

    cmd, key = argv[0], argv[1]
    lines = read_lines(key)
    pg = pages(lines)

    if cmd == "show":
        a, b = int(argv[2]), int(argv[3])
        for i in range(a, b + 1):
            print("%d [p%s]: %s" % (i, pg[i - 1], lines[i - 1]))
        return 0

    if cmd == "page":
        a, b = int(argv[2]), int(argv[3])
        for i in range(a, b + 1):
            print("%d [p%s]: %s" % (i, pg[i - 1], lines[i - 1]))
        return 0

    if cmd == "grep":
        rx = re.compile(argv[2])
        n = 0
        for i, ln in enumerate(lines, 1):
            if rx.search(ln):
                print("%d [p%s]: %s" % (i, pg[i - 1], ln.strip()))
                n += 1
        print("-- %d matches" % n)
        return 0

    print("unknown command", cmd)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
