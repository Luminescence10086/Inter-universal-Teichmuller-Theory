#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N04 independent verifier (static only).

Re-extracts every signature_verbatim from the recorded source files using the
recorded line ranges and compares byte-for-byte; recomputes every SHA256 listed in
delivery.json; checks schema/status/path-containment invariants.
Read-only: writes nothing.
"""
import csv
import hashlib
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
N04 = HERE

SRC_COMMIT = "f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb"
STATUSES = {"STATIC_COMPLETE", "EXPERIMENTAL", "PARTIAL", "UNRESOLVED", "INPUT_DRIFT"}
MAX_SUMMARY_LINES = 30
MAX_SIGNATURES = 4

fails = []
checks = 0


def check(cond, msg):
    global checks
    checks += 1
    if not cond:
        fails.append(msg)
    return cond


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    # --- delivery.json schema -------------------------------------------------
    dj_path = N04 / "delivery.json"
    if not check(dj_path.is_file(), "delivery.json missing"):
        return report()
    dj = json.loads(dj_path.read_text(encoding="utf-8"))
    for key in ("task_id", "status", "source_commit", "inputs", "outputs",
                "review_anchors", "commands_run", "new_hypotheses", "unresolved",
                "lean_run", "editor_run", "native_iut_realized", "fact_tree_admitted"):
        check(key in dj, f"delivery.json missing key: {key}")
    check(dj.get("task_id") == "N04", f"task_id != N04: {dj.get('task_id')!r}")
    check(dj.get("status") in STATUSES, f"illegal status: {dj.get('status')!r}")
    check(dj.get("source_commit") == SRC_COMMIT,
          f"source_commit mismatch: {dj.get('source_commit')!r}")
    check(dj.get("lean_run") is False, "lean_run must be false")
    check(dj.get("editor_run") is False, "editor_run must be false")
    check(dj.get("native_iut_realized") is False, "native_iut_realized must be false")
    check(dj.get("fact_tree_admitted") is False, "fact_tree_admitted must be false")

    # --- hashes of all inputs/outputs ----------------------------------------
    listed = set()
    for kind in ("inputs", "outputs"):
        for item in dj.get(kind, []):
            rel = item.get("path", "")
            check(bool(rel), f"{kind}: entry without path")
            check("sha256" in item, f"{kind}: {rel} missing sha256")
            p = (ROOT / rel).resolve()
            check(str(p).startswith(str(ROOT.resolve())), f"{kind}: path escape {rel}")
            if not check(p.is_file(), f"{kind}: missing file {rel}"):
                continue
            check(sha256(p) == item["sha256"],
                  f"{kind}: sha256 mismatch for {rel} (recorded {item['sha256']}, "
                  f"actual {sha256(p)})")
            listed.add(p)
    check("delivery.json" not in [pathlib.Path(o["path"]).name for o in dj.get("outputs", [])],
          "delivery.json must not list itself")

    # every deliverable present on disk must be hashed (no silent extras)
    for p in sorted(N04.iterdir()):
        if p.is_file() and p.name != "delivery.json":
            check(p.resolve() in listed, f"unhashed file in N04: {p.name}")

    # --- signatures.csv ------------------------------------------------------
    csv_path = N04 / "signatures.csv"
    if not check(csv_path.is_file(), "signatures.csv missing"):
        return report()
    with csv_path.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    check(len(rows) <= MAX_SIGNATURES, f"too many signatures: {len(rows)} > {MAX_SIGNATURES}")
    needed = {"id", "lean_name", "kind", "file", "line_start", "line_end", "file_sha256",
              "verbatim_sha256", "signature_verbatim", "assumptions",
              "source_claim_supported", "status"}
    if rows:
        check(needed.issubset(set(rows[0].keys())),
              f"signatures.csv missing columns: {sorted(needed - set(rows[0].keys()))}")
    for r in rows:
        sid = r.get("id")
        rel = r.get("file", "")
        src = (ROOT / rel)
        if not check(src.is_file(), f"{sid}: source file missing {rel}"):
            continue
        check(sha256(src) == r["file_sha256"],
              f"{sid}: file_sha256 drift for {rel}")
        lines = src.read_text(encoding="utf-8").splitlines()
        a, b = int(r["line_start"]), int(r["line_end"])
        check(1 <= a <= b <= len(lines), f"{sid}: bad line range {a}-{b} (file has {len(lines)})")
        block = "\n".join(lines[a - 1:b])
        check(block == r["signature_verbatim"],
              f"{sid}: signature_verbatim is NOT verbatim for {rel}:{a}-{b}")
        check(hashlib.sha256(block.encode("utf-8")).hexdigest() == r["verbatim_sha256"],
              f"{sid}: verbatim_sha256 mismatch")
        check(r["kind"] in {"def", "structure", "theorem", "abbrev"},
              f"{sid}: illegal kind {r['kind']!r}")
        check(bool(r["assumptions"].strip()), f"{sid}: empty assumptions")
        check(bool(r["source_claim_supported"].strip()), f"{sid}: empty source_claim_supported")
        check(r["status"] in {"SOURCE_FACT", "UNRESOLVED", "INPUT_DRIFT", "UNVERIFIED_MATH"},
              f"{sid}: illegal row status {r['status']!r}")
        # signature must actually name the declared lean_name's last component
        last = r["lean_name"].split("(")[0].strip().split(".")[-1].split()[-1]
        check(last in block, f"{sid}: lean_name component {last!r} not found in signature block")

    # --- SUMMARY.md length ---------------------------------------------------
    summ = N04 / "SUMMARY.md"
    if check(summ.is_file(), "SUMMARY.md missing"):
        n = len(summ.read_text(encoding="utf-8").splitlines())
        check(n <= MAX_SUMMARY_LINES, f"SUMMARY.md too long: {n} lines > {MAX_SUMMARY_LINES}")

    # --- review anchors shape ------------------------------------------------
    anchors = dj.get("review_anchors", [])
    check(1 <= len(anchors) <= 2, f"review_anchors should list at most 2 anchors, got {len(anchors)}")
    for a in anchors:
        check({"path", "line_or_page", "supports"}.issubset(a.keys()),
              f"review_anchor missing fields: {a}")

    return report()


def report():
    print(f"checks={checks} failures={len(fails)}")
    if fails:
        for f in fails:
            print("FAIL:", f)
        print("RESULT=FAIL")
        return 1
    print("RESULT=PASS (verbatim re-extraction + all hashes + schema)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
