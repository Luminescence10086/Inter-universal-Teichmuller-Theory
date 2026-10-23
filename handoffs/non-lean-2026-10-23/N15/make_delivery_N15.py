"""N15 - write delivery.json with hashes recomputed from disk (no hand-copied hash)."""

import hashlib
import json
import os

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
TDIR = "handoffs/non-lean-2026-10-23/N15"

INPUTS = [
    "research/core-backward-2026-10-23/PATH.md",
    "research/core-backward-2026-10-23/round-report.md",
    "handoffs/non-lean-task-catalog-2026-10-23.md",
    "GAP-core-comparison-reconstruction.md",
    "GAP-core-native-realization.md",
    "GAP-core-residue-hull-realization.md",
    "handoffs/core-backward-2026-10-23/fix-delivery.json",
    "handoffs/non-lean-2026-10-23/N14/receipt-review.csv",
]

OUTPUTS = [
    "SUMMARY.md",
    "status.csv",
    "candidate-graph.json",
    "patch-proposal.md",
    "make_N15.py",
    "make_delivery_N15.py",
]


def sha(p):
    h = hashlib.sha256()
    with open(os.path.join(ROOT, p), "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


doc = {
    "task_id": "N15",
    "status": "STATIC_COMPLETE",
    "source_commit": None,
    "inputs": [{"path": p, "sha256": sha(p)} for p in INPUTS],
    "outputs": [{"path": "%s/%s" % (TDIR, o), "sha256": sha("%s/%s" % (TDIR, o))} for o in OUTPUTS],
    "review_anchors": [
        {"path": "%s/status.csv" % TDIR,
         "line_or_page": "rows K4, W1, W9, T1, N04",
         "supports": "the four evidence planes are recorded separately: a delivery may pass its own CLI gate "
                     "(PASSED_GATE) while its editor receipt is graded INSUFFICIENT, STALE_HASH or absent"},
        {"path": "%s/candidate-graph.json" % TDIR,
         "line_or_page": "edges W3 -> W5 and W3 -> W6",
         "supports": "an edge is called EXISTING_RECORD only when the target's inputs[] names a path the "
                     "source's outputs[] declares, both hashed in their own delivery.json"},
        {"path": "research/core-backward-2026-10-23/PATH.md",
         "line_or_page": "lines 49-51 versus 75-82",
         "supports": "the stale-next-step finding in patch-proposal.md P1-1: one file carries two next steps"},
    ],
    "commands_run": [
        "py -3 handoffs/non-lean-2026-10-23/N15/make_N15.py   (read-only scan of 29 delivery.json; "
        "writes status.csv + candidate-graph.json; re-run reproduced both files byte for byte)",
        "py -3 handoffs/non-lean-2026-10-23/N15/make_delivery_N15.py   (recompute every input/output "
        "sha256 from disk and emit this file)",
        "py -3 -c \"...json.load per delivery.json; collect inputs[]->outputs[] matches...\"   "
        "(edge discovery; no Lean, no Lake, no editor)",
        "py -3 -c \"...csv count over N14/receipt-review.csv...\"   (6 SUPPORTED / 6 INSUFFICIENT / "
        "2 STALE / 7 MISSING over 21 graded items)",
        "git rev-parse HEAD -> 568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2   (used only to check the "
        "catalogue's HEAD line; not used as a pin)",
    ],
    "new_hypotheses": [],
    "unresolved": [
        "the workspace was live while this index was built: N09, N13 and N16 delivery records were written "
        "during the run, so every row pins its own record sha256 instead of a HEAD",
        "6 items have no delivery at all (N02, N06, N07, N08, N10, N11) and N03 has an empty directory; "
        "status.csv records them as NOT_DELIVERED / NO_DELIVERY_RECORD rather than guessing a status",
        "the per-task gap_ref column is an N15 routing proposal (no delivery.json names a GAP file: 0 hits "
        "in 29 records); it is not a source fact and must be re-decided by the main line",
        "PROPOSED edges are read off named lines of PATH.md / round-report.md / the task catalogue; no edge "
        "was verified by running Lean or by any editor observation",
        "N15 cannot close any GAP, cannot admit a fact-tree node, and cannot convert a window-level editor "
        "silence into a per-file verdict",
        "another writer put a second generator (make_N15_delivery.py, sha256 be6d5e409f4fd9f8"
        "88da084f997bd80b387fc658dc451284a90465fa7653d057) into this directory at 19:56:28; it was "
        "removed because it re-runs make_N15.py and rewrites delivery.json, which would silently replace "
        "this record. If it reappears, the two writers must be reconciled before either is trusted",
    ],
    "lean_run": False,
    "editor_run": False,
    "native_iut_realized": False,
    "fact_tree_admitted": False,
    "snapshot_inputs_hashed_elsewhere": {
        "what": "the 29 delivery.json records this index reads",
        "where": "handoffs/non-lean-2026-10-23/N15/status.csv, column delivery_json_sha256 (per row), and "
                 "candidate-graph.json, node field source_record_sha256",
        "why": "declaring them as inputs here would turn any later edit by another task into a hash failure "
               "on this package; the per-row pins keep the snapshot checkable without that coupling",
    },
}

with open(os.path.join(ROOT, TDIR, "delivery.json"), "w", encoding="utf-8") as f:
    json.dump(doc, f, ensure_ascii=False, indent=2)
    f.write("\n")

print("wrote delivery.json")
for o in OUTPUTS:
    print("  %-26s %s" % (o, sha("%s/%s" % (TDIR, o))))
