"""Assemble bundle.json from the logs actually written by the two drivers."""
import hashlib
import json
import platform
import sys
from pathlib import Path

WT = Path("D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\.wt\\e1")
OUT = Path("D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\handoffs"
           "\\round2-2026-10-23\\e1")
BASE = "484127185878e65b10795d20568bd3714eebc798"
HEAD = "24f42c645ba6ec61a693926d7956268e955a5b15"
CASE_IDS = ["E1.baseline_pass", "E1.fact_tree_removal_regression",
            "E1.unpin_entry_failure", "E1.clean_checkout_failure",
            "E1.baseline_failure", "E1.probe_exception",
            "E1.malformed_probe_result"]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


fast = json.loads((OUT / "fast-entry-runs.json").read_text(encoding="utf-8"))
checks = json.loads((OUT / "checks-run.json").read_text(encoding="utf-8"))
entry = fast[0]
suite = next(c for c in checks if c["id"] == "E1.existing_65_tests")

contract_digest = sha256(Path("D:\\Inter-universal Teichm"
                              + chr(0xFC) + "ller Theory\\handoffs\\next-round\\contracts.json"))

changes = []
for relative, purpose in (
    ("audit/mutation_harness.py",
     "reusable probe results (--reuse-probes) gated on the repository witness, so the "
     "deduplicated entry cannot reuse a verdict for different bytes; probes_reused in "
     "the report"),
    ("audit/tests/test_mutation_probe_exit.py",
     "supervised no-arg entry: file-backed streams, one total deadline covering tree "
     "cleanup (job object on Windows), exit 124 on expiry, plus --self-test-timeout, "
     "and baseline-recorded probe reuse in the focused cases"),
):
    changes.append({
        "path": relative,
        "sha256": sha256(WT / relative),
        "purpose": purpose,
    })

commands_run = [{
    "id": "E1.quick_entry",
    "argv": entry["argv"],
    "cwd": entry["cwd"],
    "exit_code": entry["exit_code"],
    "seconds": entry["seconds"],
    "attempt": entry["attempt"],
    "attempts_made": len(fast),
    "log": entry["stdout_path"],
    "log_sha256": entry["stdout_sha256"],
    "stdout_path": entry["stdout_path"],
    "stdout_sha256": entry["stdout_sha256"],
    "stderr_path": entry["stderr_path"],
    "stderr_sha256": entry["stderr_sha256"],
    "note": ("the frozen quick entry, measured from an independent parent: exit status "
             "is this parent's own wait() result, never a log's last line"),
}] + [{
    "id": c["id"],
    "argv": c["argv"],
    "cwd": c["cwd"],
    "exit_code": c["exit_code"],
    "expected_exit": c["expected_exit"],
    "seconds": c["seconds"],
    "log": c["stdout_path"],
    "log_sha256": c["stdout_sha256"],
    "stdout_path": c["stdout_path"],
    "stdout_sha256": c["stdout_sha256"],
    "stderr_path": c["stderr_path"],
    "stderr_sha256": c["stderr_sha256"],
    "note": c["note"],
} for c in checks]

checks_out = [{
    "id": case_id,
    "argv": entry["argv"],
    "cwd": entry["cwd"],
    "exit_code": entry["exit_code"],
    "elapsed_seconds": entry["seconds"],
    "stdout_path": entry["stdout_path"],
    "stdout_sha256": entry["stdout_sha256"],
    "stderr_path": entry["stderr_path"],
    "stderr_sha256": entry["stderr_sha256"],
    "outcome": "PASS" if entry["exit_code"] == 0 else "FAIL",
    "executed_as": "E1.quick_entry",
} for case_id in CASE_IDS]
checks_out.append({
    "id": "E1.existing_65_tests",
    "argv": suite["argv"],
    "cwd": suite["cwd"],
    "exit_code": suite["exit_code"],
    "elapsed_seconds": suite["seconds"],
    "stdout_path": suite["stdout_path"],
    "stdout_sha256": suite["stdout_sha256"],
    "stderr_path": suite["stderr_path"],
    "stderr_sha256": suite["stderr_sha256"],
    "outcome": suite["outcome"],
    "executed_as": "E1.existing_65_tests",
})

bundle = {
    "schema": 1,
    "status": "REPAIR_READY_FOR_REVIEW" if entry["exit_code"] == 0 else "INCOMPLETE",
    "task_id": "E1",
    "base_commit": BASE,
    "head_commit": HEAD,
    "scope_contract_sha256": contract_digest,
    "source_tree_clean": True,
    "environment": {
        "os": f"{platform.system()} {platform.release()} ({platform.version()})",
        "python": f"{platform.python_version()} ({sys.executable})",
        "lean": None,
        "lake": None,
        "dependency_locks": [],
        "notes": [
            "no Lean build and no editor observation in this task",
            "TEMP/TMP were pointed inside the worktree (.wt/e1/.tmp) and a "
            "sitecustomize shim that only drops the mode argument of os.mkdir was on "
            "PYTHONPATH, because this sandbox refuses writes inside mkdtemp(0o700) "
            "directories; neither is part of the commit",
            f"E1.existing_65_tests needed PYTHONIOENCODING=utf-8 in this umlaut path",
        ],
    },
    "changed_paths": [c["path"] for c in changes],
    "changes": changes,
    "commands_run": commands_run,
    "checks": checks_out,
    "deduplication": {
        "matrix": ("M1-M8 runs once, in E1.baseline_pass; the focused cases use "
                   "--probes-only"),
        "probes": ("the healthy probes run for real once, in E1.baseline_pass; the "
                   "focused cases reuse those recorded results with --reuse-probes "
                   "only after the harness re-checks the repository witness, and the "
                   "injected probe always runs for real"),
        "frozen_case_ids": ("the seven probe cases are one execution (E1.quick_entry); "
                            "the runner never re-runs the entry per case"),
    },
    "mathematics": {
        "candidate_only": True,
        "theorems": [],
        "cli_zero_diagnostics": None,
        "vscode_observation": None,
        "reviewer_vscode_replay_complete": False,
        "new_formal_admissions": 0,
    },
    "open_obligations": [
        "E1.existing_65_tests is green here only with PYTHONIOENCODING=utf-8: "
        "test_tcb_manifest.test_help_and_json (E3-owned, untouched) decodes a child "
        "process with the console code page while this worktree path contains 'ü'.",
    ],
    "unresolved": [
        ("reviewer-side replay environment: this delivery was measured in a sandbox "
         "that denies writes inside mkdtemp(0o700) directories, so a sitecustomize "
         "shim (os.mkdir mode only) and an in-worktree TEMP were used; the reviewer's "
         "D:/iut-wt/e1 replay needs neither"),
        ("taskkill /T /F is refused (Access denied) in this sandbox and left a "
         "grandchild alive; the entry therefore kills via a Windows job object "
         "(KILL_ON_JOB_CLOSE + TerminateJobObject), verified by --self-test-timeout"),
        ("the single error in the un-flagged suite run is the pre-existing "
         "test_tcb_manifest encoding failure described above, not this commit"),
    ],
    "limitations": [
        "PASS here means the exit-code contract of the required probes holds; it does "
        "not certify any Python program, any Lean build, or any mathematical claim",
        "no Lean run, no VS Code observation, no fact-tree/pin/receipt change",
        "the pre-repair entry measured 167.3 s wall clock in this worktree with the "
        "same 7/7 output, i.e. already past the reviewer's 150 s budget",
    ],
    "lean_run": None,
    "editor_run": None,
    "summary_path": "SUMMARY.md",
}

(OUT / "bundle.json").write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + "\n",
                                 encoding="utf-8")
print(json.dumps({"status": bundle["status"],
                  "quick_entry": {"exit_code": entry["exit_code"],
                                  "seconds": entry["seconds"]},
                  "checks": {c["id"]: c["outcome"] for c in checks_out}},
                 ensure_ascii=False, indent=2))
