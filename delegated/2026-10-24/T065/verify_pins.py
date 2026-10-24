#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""T065 · line-pin re-verification for the Kummer provenance table.

Read-only. Re-reads the pinned Lean checkout and prints, for every
(file, line) pin used by SUMMARY.md, the exact source line and the file
SHA256, so that no line number in the summary is asserted from memory.

Usage: python verify_pins.py --root <repo> [--json out.json]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

BASE = os.path.join("reviews", "core-round", "external", "iut")

PINS = [
    ("Iut/LogLink/StripKummer.lean",
     [127, 138, 145, 150, 168, 170, 172, 174, 176, 178, 185, 189, 192, 206, 218]),
    ("Iut/LogLink/GalKummer.lean",
     [215, 231, 238, 361, 363, 365, 368, 370, 372, 379, 396, 412, 415, 428]),
    ("Iut/LogLink/Kummer.lean", [158, 162, 248, 250, 252, 294, 300]),
    ("Iut/HodgeTheater/StripLift.lean", [428, 430, 432, 438, 443]),
    ("Iut/LogLink/GalKummerAll.lean", [535, 537, 539, 544, 546, 548, 550, 557, 560, 635]),
    ("Iut/LogLink/Thm311Rest.lean", [164, 181]),
    ("Iut/HodgeTheater/PrimeStrip.lean", [227]),
    ("Iut/Wall/Scaling.lean", [121, 123]),
    ("Iut/Wall/MultiContainer.lean", [114, 118]),
]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json")
    args = ap.parse_args()
    root = os.path.abspath(args.root)

    report, missing = [], 0
    for rel, lines in PINS:
        path = os.path.join(root, BASE, rel)
        if not os.path.exists(path):
            missing += 1
            report.append({"file": rel, "present": False})
            continue
        src = open(path, encoding="utf-8").read().splitlines()
        entry = {
            "file": rel,
            "present": True,
            "bytes": os.path.getsize(path),
            "lines": len(src),
            "sha256": sha256(path),
            "pins": [],
        }
        for n in lines:
            text = src[n - 1].rstrip() if 0 < n <= len(src) else None
            entry["pins"].append({"line": n, "text": text, "ok": text is not None})
        report.append(entry)

    out = {"files": report, "files_present": missing == 0,
           "pins_total": sum(len(v) for _, v in PINS), "files_missing": missing}
    text = json.dumps(out, ensure_ascii=False, indent=2)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
    sys.stdout.write(text + "\n")
    return 0 if missing == 0 else 2


if __name__ == "__main__":
    sys.exit(main())
