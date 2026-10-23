#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N02 mechanical anchor check (read-only, no network, no Lean).

For every anchor claimed in controversies.csv, this script:
  1. locates the quoted snippet in the local file (single line, whitespace-normalised);
  2. reports the line it was found on and, for IUT III / LANA, the PDF page taken
     from the '===== PDF PAGE n =====' / '===== PAGE n =====' marker;
  3. compares both with the line range written in the CSV.

It prints PASS/FAIL per check and a summary. Exit code 1 if any FAIL.
Nothing is written.

Usage:  py -3 verify_N02.py
"""
import re
import sys

ROOT = "D:\\Inter-universal Teichm\u00fcller Theory\\"
FILES = {
    "iut3": ROOT + r"research\round2-source-cache\iut-III-official-retrieved-2026-10-16.txt",
    "lana": ROOT + r"research\round2-source-cache\LANA-interim-report-2026-07.txt",
    "ss": ROOT + r"reviews\core-round\external\DrAbx123--Formalization-of-Inter-universal-"
          r"Teichmuller-Theory-IUT-and-abc-conjecture\vendor\promachina\snapshots\0d52e0fd5b53"
          r"\docs\scholze-stix-why-abc-is-still-a-conjecture.md",
    "rpt2018": ROOT + r"reviews\core-round\external\DrAbx123--Formalization-of-Inter-universal-"
               r"Teichmuller-Theory-IUT-and-abc-conjecture\papers\motizuki_corpus\text\Rpt2018.txt",
}

# (row id, side, filekey, line_lo, line_hi, expected_page_or_None, snippet)
CHECKS = [
    ("C01", "B", "iut3", 11073, 11083, "184", "then follows formally"),
    ("C01", "A", "ss", 661, 662, None, "omit the scalars j"),
    ("C02", "A", "ss", 554, 557, None, "necessity of this scaling is critical"),
    ("C02", "A", "ss", 572, 573, None, "does not properly distinguish them"),
    ("C02", "B", "iut3", 9780, 9794, "159", "alien arithmetic holomorphic"),
    ("C02", "B", "iut3", 11016, 11019, "183", "localizations of arithmetic vector bundles"),
    ("C03", "A", "ss", 631, 632, None, "does not become false, but trivial"),
    ("C03", "B", "iut3", 668, 684, "12", "upper semi-compatibility"),
    ("C03", "B", "iut3", 9344, 9345, "153", "procession-normalized"),
    ("C04", "A", "ss", 578, 596, None, "forgets about the concrete embeddings"),
    ("C04", "A", "ss", 620, 629, None, "one must consistently identify"),
    ("C04", "B", "iut3", 31, 37, "1", "alien arithmetic holomorphic structure"),
    ("C04", "B", "iut3", 9797, 9821, "159", "Although the various versions of the"),
    ("C05", "A", "ss", 649, 660, None, "monodromy j"),
    ("C05", "B", "rpt2018", 1559, 1580, None, "omitting the labels"),
    ("C05", "B", "rpt2018", 1557, 1590, None, "erroneous operation of"),
    ("C06", "A", "ss", 635, 667, None, "blurring must be by a factor"),
    ("C06", "A", "lana", 2172, 2213, "47", "Scholze-Stix hexagon"),
    ("C06", "B", "lana", 2216, 2226, "48", "obtained by comparing the volumes of two pilots"),
    ("C06", "B", "lana", 2240, 2243, "48", "these two objects lie on the"),
    ("C07", "A", "ss", 574, 576, None, "forming averages when one extracts numbers"),
    ("C07", "A", "ss", 657, 659, None, "overcome by using averages"),
    ("C07", "B", "iut3", 7005, 7010, "116", "taking theaverage"),
    ("C07", "B", "iut3", 7247, 7271, "120", "The answer to this"),
    ("C08", "A", "ss", 163, 171, None, "minus the absolute values of the logarithm"),
    ("C08", "B", "iut3", 6974, 7017, "115", "corresponds to adding"),
    ("C09", "A", "ss", 616, 619, None, "identification of concrete"),
    ("C09", "B", "iut3", 10498, 10513, "173", "union of thepossible images"),
    ("C09", "B", "iut3", 8190, 8208, "134", "Independence of the"),
    ("C10", "A", "ss", 616, 619, None, "without which the conclusion"),
    ("C10", "B", "iut3", 10512, 10520, "174", "donot regard as subject"),
    ("C11", "A", "ss", 222, 224, None, "essentially free of content"),
    ("C11", "A", "ss", 661, 662, None, "empty inequality"),
    ("C11", "B", "iut3", 10526, 10528, "174", "for any real number"),
    ("C11", "B", "lana", 2114, 2116, "45", "only upper semi-compatible"),
    ("C12", "A", "lana", 2126, 2141, "46", "exists some suitable"),
    ("C12", "A", "lana", 2279, 2282, "49", "do not have a proof of (9-1)"),
    ("C12", "B", "iut3", 11084, 11088, "184", "yields two tautologically equivalent ways"),
]


def load(key):
    with open(FILES[key], "rb") as fh:
        text = fh.read().decode("utf-8", errors="replace")
    lines = text.splitlines()
    pages = []
    cur = None
    for ln in lines:
        m = re.match(r"^===== (?:PDF )?PAGE (\d+) =====\s*$", ln.strip())
        if m:
            cur = m.group(1)
        pages.append(cur)
    return lines, pages


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    cache = {}
    bad = 0
    for rid, side, key, lo, hi, page, snip in CHECKS:
        if key not in cache:
            cache[key] = load(key)
        lines, pages = cache[key]
        hit = None
        for i in range(lo - 1, min(hi, len(lines))):
            if snip in lines[i]:
                hit = i + 1
                break
        if hit is None:
            bad += 1
            print("FAIL %-4s %s %-7s [%d-%d] snippet not found: %r"
                  % (rid, side, key, lo, hi, snip))
            continue
        got_page = pages[hit - 1] or "-"
        ok = (page is None) or (got_page == page)
        if not ok:
            bad += 1
        print("%s %-4s %s %-7s line %-6d page %-4s expected page %-4s  %r"
              % ("PASS" if ok else "FAIL", rid, side, key, hit, got_page,
                 page or "-", snip))
    print("-- %d checks, %d FAIL" % (len(CHECKS), bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
