"""Run the E1 delivery checks that are not the frozen fast entry, and time them.

Every row records the parent's own ``wait()`` status, so no exit code comes from a
log's last line.  Streams go to files.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

WT = Path("D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\.wt\\e1")
OUT = Path("D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\handoffs"
           "\\round2-2026-10-23\\e1")
LOGS = OUT / "logs"
PY = sys.executable
TOOLS = OUT
CHECKS = [
    {
        "id": "E1.self_test_timeout",
        "argv": [PY, "-B", "audit/tests/test_mutation_probe_exit.py",
                 "--self-test-timeout"],
        "expected_exit": 0,
        "note": ("supervises a child that spawns a grandchild holding the inherited "
                 "handles and never returns; requires exit 124, a wall clock inside "
                 "the deadline, and a reaped grandchild"),
    },
    {
        "id": "E1.negative_control",
        "argv": [PY, "-B", str(TOOLS / "negative_control.py")],
        "expected_exit": 1,
        "note": ("reintroduces the round-1 defect (probe_violations returns nothing); "
                 "6 of 7 cases must then fail, so the cases still catch it"),
    },
    {
        "id": "E1.exit_contract_propagation",
        "argv": [PY, "-B", str(TOOLS / "exit_contracts.py")],
        "expected_exit": 0,
        "note": ("supervisor relays a nonzero child status (7) and a forged reuse "
                 "witness is refused with exit 2"),
    },
    {
        "id": "E1.existing_65_tests",
        "argv": [PY, "-B", "-m", "unittest", "discover", "-s", "audit/tests",
                 "-p", "test_*.py", "-v"],
        "expected_exit": 0,
        "note": ("72 tests = 65 pre-existing + 7 E1 cases; needs PYTHONIOENCODING=utf-8 "
                 "in this umlaut path, see unresolved"),
        "env": {"PYTHONIOENCODING": "utf-8"},
    },
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


rows = []
for check in CHECKS:
    slug = check["id"].replace(".", "-")
    stdout_path = LOGS / f"{slug}.stdout.txt"
    stderr_path = LOGS / f"{slug}.stderr.txt"
    env = dict(os.environ)
    env.update(check.get("env", {}))
    started = time.monotonic()
    with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
        process = subprocess.Popen(check["argv"], cwd=str(WT), stdin=subprocess.DEVNULL,
                                   stdout=out, stderr=err, env=env)
        code = process.wait()
    seconds = round(time.monotonic() - started, 2)
    row = {
        "id": check["id"],
        "argv": check["argv"],
        "cwd": str(WT),
        "exit_code": code,
        "expected_exit": check["expected_exit"],
        "outcome": "PASS" if code == check["expected_exit"] else "FAIL",
        "seconds": seconds,
        "stdout_path": str(stdout_path.relative_to(OUT)),
        "stdout_sha256": sha256(stdout_path),
        "stderr_path": str(stderr_path.relative_to(OUT)),
        "stderr_sha256": sha256(stderr_path),
        "env": check.get("env", {}),
        "note": check["note"],
    }
    rows.append(row)
    print(json.dumps(row, ensure_ascii=False), flush=True)

(OUT / "checks-run.json").write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n",
                                    encoding="utf-8")
sys.exit(0 if all(r["outcome"] == "PASS" for r in rows) else 1)
