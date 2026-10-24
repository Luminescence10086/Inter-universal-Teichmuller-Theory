"""T097 — Wall (9-1) quantifier ledger verifier (read-only, offline, idempotent).

Reads the baseline-pinned sources under the repo root and mechanically checks every
citation recorded in quantifiers.json:

  * each (file, line, needle) anchor really occurs on that line,
  * each (file, line, page) anchor really lies inside the PDF page marker it claims,
  * each (file, span, needles) block really contains all its needles in order,
  * every recorded file SHA256 / byte count still matches the bytes on disk.

It prints JSON to stdout and writes nothing except the log the caller redirects.
It never writes into the repo, never calls the network, never runs Lean.

Exit 0 = all anchors verified.  Exit 2 = at least one anchor failed.
Status of the deliverable is RESEARCH_ONLY regardless of the exit code: this
script checks that a transcription is faithful to its cited bytes. It does not
check, and does not claim, that Wall (9-1) is true.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAGE_RE = re.compile(r"^=+ *(?:PDF )?PAGE (\d+) *=+$")


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Source:
    def __init__(self, root, rel):
        self.rel = rel
        self.path = os.path.join(root, rel.replace("/", os.sep))
        self.exists = os.path.isfile(self.path)
        self.lines = []
        self.sha256 = None
        self.bytes = None
        if self.exists:
            with open(self.path, "rb") as fh:
                raw = fh.read()
            self.bytes = len(raw)
            self.sha256 = hashlib.sha256(raw).hexdigest()
            text = raw.decode("utf-8", errors="replace")
            self.lines = text.split("\n")

    def line(self, n):
        return self.lines[n - 1] if 1 <= n <= len(self.lines) else None

    def page_of(self, n):
        """PDF/printed page number of line n, from the nearest 'PAGE n' marker above."""
        for i in range(min(n, len(self.lines)) - 1, -1, -1):
            m = PAGE_RE.match(self.lines[i].strip())
            if m:
                return int(m.group(1))
        return None


def verify(ledger, root):
    cache = {}
    failures = []
    checks = 0

    def src(rel):
        if rel not in cache:
            cache[rel] = Source(root, rel)
            if not cache[rel].exists:
                failures.append({"check": "file_present", "file": rel, "detail": "missing on disk"})
        return cache[rel]

    # 1. recorded hashes of the pinned inputs
    for rel, rec in sorted(ledger["input_hashes"].items()):
        s = src(rel)
        checks += 1
        if s.sha256 != rec["sha256"]:
            failures.append({"check": "input_sha256", "file": rel,
                             "expected": rec["sha256"], "actual": s.sha256})
        checks += 1
        if s.bytes != rec["bytes"]:
            failures.append({"check": "input_bytes", "file": rel,
                             "expected": rec["bytes"], "actual": s.bytes})

    # 2. single-line anchors: file + line + needle
    for a in ledger["anchors"]:
        s = src(a["file"])
        checks += 1
        text = s.line(a["line"])
        if text is None:
            failures.append({"check": "anchor_line", "id": a["id"], "file": a["file"],
                             "line": a["line"], "detail": "line out of range"})
            continue
        if a["needle"] not in text:
            failures.append({"check": "anchor_needle", "id": a["id"], "file": a["file"],
                             "line": a["line"], "needle": a["needle"],
                             "actual": text[:180]})

    # 3. page anchors: the line must sit inside the page it claims
    for a in ledger["page_anchors"]:
        s = src(a["file"])
        checks += 1
        actual_page = s.page_of(a["line"])
        if actual_page != a["page"]:
            failures.append({"check": "page_anchor", "id": a["id"], "file": a["file"],
                             "line": a["line"], "expected_page": a["page"],
                             "actual_page": actual_page})

    # 4. span anchors: all needles present, in the given order, inside [start, end]
    for a in ledger["span_anchors"]:
        s = src(a["file"])
        checks += 1
        if not (1 <= a["start"] <= a["end"] <= len(s.lines) + 1):
            failures.append({"check": "span_range", "id": a["id"], "file": a["file"],
                             "start": a["start"], "end": a["end"]})
            continue
        block = "\n".join(s.lines[a["start"] - 1:a["end"]])
        pos = 0
        for needle in a["needles"]:
            checks += 1
            found = block.find(needle, pos)
            if found < 0:
                failures.append({"check": "span_needle", "id": a["id"], "file": a["file"],
                                 "span": [a["start"], a["end"]], "needle": needle,
                                 "detail": "absent, or out of order"})
                break
            pos = found + len(needle)

    # 5. the hard requirement: the order must be (fix input) then exists S,
    #    and no pinned source may contain the forbidden forall-over-S form.
    order = ledger["quantifier_chain"]["order"]
    checks += 1
    if order != ["FIX_INPUT", "EXISTS_iota", "EXISTS_S", "EQ"]:
        failures.append({"check": "quantifier_order", "actual": order})

    # 5b. the exists must be NESTED INSIDE the forall in the Lean wall, i.e. the forall
    #     binder must precede the exists binder in the source. This is the mechanical
    #     form of "must not be read as exists S for all inputs".
    wall_file = "reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean"
    s = src(wall_file)
    checks += 1
    body = "\n".join(s.lines[172:175])  # EtaAlg.lean lines 173-175
    i_forall, i_exists = body.find("∀ (h₁"), body.find("∃ (ι")
    if not (0 <= i_forall < i_exists):
        failures.append({"check": "nesting_order", "file": wall_file,
                         "forall_at": i_forall, "exists_at": i_exists,
                         "detail": "the forall over the input must precede the exists"})

    forbidden = ledger["forbidden_forms"]
    for rel in forbidden["scanned_files"]:
        s = src(rel)
        for pat in forbidden["regexes"]:
            checks += 1
            hit = re.search(pat, "\n".join(s.lines))
            if hit:
                failures.append({"check": "forbidden_form", "file": rel,
                                 "regex": pat, "match": hit.group(0)[:120]})

    return {
        "task_id": ledger["task_id"],
        "verdict": "ALL_ANCHORS_VERIFIED" if not failures else "ANCHORS_FAILED",
        "checks_run": checks,
        "checks_failed": len(failures),
        "failures": failures,
        "scope": ("Byte-level transcription audit only. No Lean run, no proof of (9-1), "
                  "no claim about Corollary 3.12 or abc."),
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=os.path.abspath(os.path.join(HERE, "..", "..", "..")),
                    help="repo root that holds the baseline-pinned sources")
    ap.add_argument("--ledger", default=os.path.join(HERE, "quantifiers.json"))
    args = ap.parse_args(argv)

    with io.open(args.ledger, encoding="utf-8") as fh:
        ledger = json.load(fh)
    result = verify(ledger, args.root)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["verdict"] == "ALL_ANCHORS_VERIFIED" else 2


if __name__ == "__main__":
    sys.exit(main())
