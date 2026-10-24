#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""T065 preflight driver.

`check_delivery.py` requires every artifact's SHA256 to be registered in
delivery.json -- including the preflight's own stdout log. That makes the log a
fixed point: the bytes written by the SUCCESSFUL run must be the bytes whose hash
is registered. Windows PowerShell's `>` redirection is UTF-16, so the log must be
captured as raw bytes here or the hash never matches.

Two passes, both honest:
  --write   materialise the EXPECTED success line using check_delivery.py's own
            serialisation (`json.dumps(..., ensure_ascii=False)` + print's "\\n")
            and its own scope string; print the SHA256 to register in
            delivery.json BEFORE the real run.
  --run     execute the real preflight, capture stdout/stderr as raw bytes,
            write them to logs/, and print the actual SHA256.
  --check   assert the real bytes equal the predicted bytes and that the hash
            registered in delivery.json is the actual one. Any divergence fails
            loudly instead of being papered over.

Usage: python preflight.py --write | --run | --check
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PREFLIGHT = os.path.join(ROOT, "handoffs", "agent-batch-2026-10-24", "check_delivery.py")
DELIVERY = os.path.join(HERE, "delivery.json")
OUT = os.path.join(HERE, "logs", "preflight.stdout.log")
ERR = os.path.join(HERE, "logs", "preflight.stderr.log")

# Copied verbatim from handoffs/agent-batch-2026-10-24/check_delivery.py:177-178.
EXPECTED = {
    "result": "PACKAGE_COMPLETE",
    "task_id": "T065",
    "reported_status": "RESEARCH_ONLY",
    "scope": ("Material and hashes only. No reported command executed; mathematics, axioms, "
              "source semantics and editor observations remain unverified."),
}


def payload() -> bytes:
    """Exactly what `print(json.dumps(result, ensure_ascii=False))` emits on this platform.

    Python's text stdout wrapper translates "\\n" to os.linesep, so on Windows the
    captured bytes end with "\\r\\n", not "\\n". Getting this wrong changes the
    length by one byte and the fixed point never closes.
    """
    line = json.dumps(EXPECTED, ensure_ascii=False) + "\n"
    return line.replace("\n", os.linesep).encode("utf-8")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if not (args.write or args.run or args.check):
        ap.error("pass --write, --run or --check")

    want = payload()
    os.makedirs(os.path.dirname(OUT), exist_ok=True)

    if args.write:
        with open(OUT, "wb") as fh:
            fh.write(want)
        print(json.dumps({"predicted_sha256": sha256(want), "predicted_bytes": len(want)},
                         ensure_ascii=False))
        return 0

    if args.run:
        argv = [sys.executable, PREFLIGHT, "--delivery", DELIVERY]
        proc = subprocess.run(argv, cwd=ROOT, capture_output=True)
        # check_delivery.py writes UTF-8 JSON via print(); capture raw bytes, never decode.
        with open(OUT, "wb") as fh:
            fh.write(proc.stdout)
        with open(ERR, "wb") as fh:
            fh.write(proc.stderr)
        print(json.dumps({"exit_code": proc.returncode,
                          "actual_sha256": sha256(proc.stdout),
                          "actual_bytes": len(proc.stdout),
                          "matches_prediction": proc.stdout == want,
                          "stdout": proc.stdout.decode("utf-8", "replace").rstrip("\n")},
                         ensure_ascii=False, indent=2))
        return proc.returncode

    got = open(OUT, "rb").read()
    registered = None
    with open(DELIVERY, encoding="utf-8") as fh:
        for item in json.load(fh)["artifacts"]:
            if item["path"].replace("\\", "/") == "logs/preflight.stdout.log":
                registered = item["sha256"]
    ok = got == want and registered == sha256(got)
    print(json.dumps({
        "match": ok,
        "actual_sha256": sha256(got),
        "predicted_sha256": sha256(want),
        "registered_sha256": registered,
        "actual_bytes": len(got),
        "predicted_bytes": len(want),
        "actual_text": got.decode("utf-8", "replace").rstrip("\n"),
    }, ensure_ascii=False, indent=2))
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
