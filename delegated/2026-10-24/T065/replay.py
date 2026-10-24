#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""T065 replay: regenerate the field-provenance evidence and re-verify every source pin.

Replays exactly two explicit targets, in this order:
  1. trace_fields.py  -> logs/fields.json   (machine-readable provenance rows)
  2. verify_pins.py   -> logs/pins.json     (exact source line at every pinned line number)

No downloads, no upgrades, no writes outside delegated/2026-10-24/T065/, no main-project
mutation. Output is deterministic (no timestamps), so run 1 and run 2 of this script must be
byte-identical.

Usage: python replay.py [--root <repo>] [--out logs]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# SHA256 of every upstream source file this task reads. Recomputed, never trusted.
PINS = {
    "reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean":
        ("a7b091c5cd076112ce3ea1151dcc4137a81ebd2e4d746781ec36ada953368049", 252),
    "reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean":
        ("1dd1a56eff40a021f1de9835d7172706a6240495d7e27ef9cb1db7beec4f2e55", 460),
    "reviews/core-round/external/iut/Iut/LogLink/Kummer.lean":
        ("c250443ede2e12be428f7e84ec7b61aab82eab724a1134358152eccdb877e4e4", 312),
    "reviews/core-round/external/iut/Iut/HodgeTheater/StripLift.lean":
        ("cd8fe6448d3a6d96e9988b38618ceefb0518baf6d0a93b8d73f261c229bd21b4", 533),
    "reviews/core-round/external/iut/Iut/LogLink/GalKummerAll.lean":
        ("990ec0689c1b54164becdad7ba3eb22a9d8bd486b762243625db46706f60ed29", 676),
    "reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean":
        ("01d439345e489cc92be6e19db7e2b30a9a9536f788244aaa69a2066de3a69a2d", 585),
    "reviews/core-round/external/iut/Iut/HodgeTheater/PrimeStrip.lean":
        ("90653fa9c7e5efba402134a079b1267373affb22a8ee89264b15dffa796cb598", 531),
    "reviews/core-round/external/iut/Iut/Wall/Scaling.lean":
        ("1624cabcd42c0a25f43898b0015fba1fc4517e0c2424fd7e22b4a8147330d4a4", 439),
    "reviews/core-round/external/iut/Iut/Wall/MultiContainer.lean":
        ("a1aef71ec5fefbd4fe809eae537ff9e258bdb9297ce9319c06d3efed89960597", 513),
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(argv, cwd, out_path, err_path):
    env = dict(os.environ, PYTHONIOENCODING="utf-8")
    proc = subprocess.run(argv, cwd=cwd, capture_output=True, env=env)
    with open(out_path, "wb") as fh:
        fh.write(proc.stdout)
    with open(err_path, "wb") as fh:
        fh.write(proc.stderr)
    return proc.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default=os.path.join(HERE, "logs"))
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)

    steps = [
        ("trace_fields", "trace_fields.py", "fields.json"),
        ("verify_pins", "verify_pins.py", "pins.json"),
    ]
    codes = {}
    for name, script, json_name in steps:
        codes[name] = run(
            [sys.executable, os.path.join(HERE, script), "--root", root,
             "--json", os.path.join(out, json_name)],
            cwd=root,
            out_path=os.path.join(out, name + ".stdout.log"),
            err_path=os.path.join(out, name + ".stderr.log"),
        )

    checks, failed = [], 0
    for rel, (want_sha, want_lines) in PINS.items():
        path = os.path.join(root, rel)
        if not os.path.exists(path):
            checks.append({"file": rel, "ok": False, "reason": "missing"})
            failed += 1
            continue
        got = sha256(path)
        with open(path, encoding="utf-8") as fh:
            n = len(fh.read().splitlines())
        ok = got == want_sha and n == want_lines
        failed += 0 if ok else 1
        checks.append({"file": rel, "ok": ok, "sha256": got, "lines": n})

    fields_json = os.path.join(out, "fields.json")
    report = {
        "result": "PINS_OK" if failed == 0 and all(c == 0 for c in codes.values())
                  else "PINS_FAILED",
        "scripts": [{"name": n, "exit_code": codes[n]} for n, _, _ in steps],
        "pins_checked": len(PINS),
        "pins_failed": failed,
        "files": checks,
        "fields_json_sha256": sha256(fields_json) if os.path.exists(fields_json) else None,
        "pins_json_sha256": sha256(os.path.join(out, "pins.json"))
                            if os.path.exists(os.path.join(out, "pins.json")) else None,
        "lean_build_performed": False,
        "scope": "Read-only source tracing and line-pin re-hashing. Nothing was compiled.",
    }
    sys.stdout.write(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return 0 if report["result"] == "PINS_OK" else 2


if __name__ == "__main__":
    sys.exit(main())
