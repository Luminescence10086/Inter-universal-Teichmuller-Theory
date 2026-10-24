"""T097 delivery.json builder.

Reads the real artifacts on disk, recomputes their SHA256, reads the real run record
(logs/audit.run.json) written by replay.ps1, and emits delivery.json.

Nothing here is hand-typed: hashes, exit code and duration come from the files.
"""
from __future__ import annotations

import hashlib
import io
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))

ARTIFACTS = [
    ("SUMMARY.md", "summary"),
    ("quantifiers.json", "source_ledger"),
    ("T097_audit.py", "verifier"),
    ("replay.ps1", "replay"),
    ("sources.v1-draft.json.superseded", "superseded_draft_marker"),
    ("logs/audit.stdout.log", "stdout"),
    ("logs/audit.stderr.log", "stderr"),
    ("logs/audit.run.json", "run_record"),
    ("logs/replay.argv.log", "argv"),
    ("logs/replay.pins.log", "replay_pins"),
    ("logs/negative_control.log", "negative_control"),
]


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def main():
    with io.open(os.path.join(HERE, "quantifiers.json"), encoding="utf-8-sig") as fh:
        ledger = json.load(fh)
    with io.open(os.path.join(HERE, "logs", "audit.run.json"), encoding="utf-8-sig") as fh:
        run = json.load(fh)

    artifacts = []
    for rel, role in ARTIFACTS:
        p = os.path.join(HERE, rel.replace("/", os.sep))
        if os.path.isfile(p):
            artifacts.append({"path": rel, "sha256": sha(p), "role": role})

    upstream = [
        {"path": k, "sha256": v["sha256"]}
        for k, v in sorted(ledger["input_hashes"].items())
    ]

    delivery = {
        "schema_version": 1,
        "task_id": "T097",
        "task_card_sha256": "4f2d1b1a581d9fb26e6191e3cccc4c090dd25295fcac707529b438364a2a0265",
        "baseline_sha256": "e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf",
        "status": "RESEARCH_ONLY",
        "summary_file": "SUMMARY.md",
        "gap_file": None,
        "replay_file": "replay.ps1",
        "base_commit": "8d60456043e30a3da79cc838d03a19b80675dc98",
        "returned_commit": None,
        "artifacts": artifacts,
        "declarations": [],
        "runs": [
            {
                "kind": "audit",
                "argv": run["argv"],
                "cwd": run["cwd"],
                "exit_code": run["exit_code"],
                "duration_seconds": run["duration_seconds"],
                "stdout": run["stdout"],
                "stderr": run["stderr"],
                "inputs": [
                    {"path": "T097_audit.py", "sha256": sha(os.path.join(HERE, "T097_audit.py"))},
                    {"path": "quantifiers.json", "sha256": sha(os.path.join(HERE, "quantifiers.json"))},
                ],
            }
        ],
        "dependency_deliveries": [],
        "upstream_inputs": upstream,
        "editor": {"performed": False, "evidence_file": None, "source_sha256": None},
        "lean": {
            "performed": False,
            "reason": "T097 is SOURCE_OR_ENGINEERING. The Lean signatures are quoted as text from "
                      "the baseline-pinned files; no lake/lean invocation was made, so no "
                      "compilation, axiom or editor claim is made here.",
        },
        "scope_note": (
            "RESEARCH_ONLY source transcription. The recorded run re-checks that every quoted "
            "sentence really sits at the cited file/line/page of the pinned sources. It does NOT "
            "prove (9-1), does NOT verify Corollary 3.12 or abc, and is NOT a Lean or editor "
            "acceptance. The source itself states it has no proof of (9-1) (LANA p.49)."
        ),
    }

    out = os.path.join(HERE, "delivery.json")
    with io.open(out, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(delivery, fh, ensure_ascii=False, indent=2)
        fh.write("\n")
    print(json.dumps({"wrote": "delivery.json", "artifacts": len(artifacts),
                      "upstream_inputs": len(upstream),
                      "run_exit_code": run["exit_code"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
