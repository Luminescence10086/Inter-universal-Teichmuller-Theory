"""Measure the frozen fast entry from an independent parent process.

The exit status recorded here is this parent's own ``wait()`` result, not the last
line of the child's stdout.  Streams go to files rather than pipes, so no inherited
handle can stall the collection the way the round-1 replay was stalled.
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
ARGV = [sys.executable, "-B", "audit/tests/test_mutation_probe_exit.py"]
MAX_ATTEMPTS = 3  # one measured run plus at most two retries


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def one_attempt(index):
    stdout_path = LOGS / f"e1-fast-entry.{index}.stdout.txt"
    stderr_path = LOGS / f"e1-fast-entry.{index}.stderr.txt"
    started = time.monotonic()
    with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
        process = subprocess.Popen(ARGV, cwd=str(WT), stdin=subprocess.DEVNULL,
                                   stdout=out, stderr=err, env=dict(os.environ))
        code = process.wait()
    seconds = round(time.monotonic() - started, 2)
    return {
        "attempt": index,
        "argv": ARGV,
        "cwd": str(WT),
        "exit_code": code,
        "seconds": seconds,
        "stdout_path": str(stdout_path.relative_to(OUT)),
        "stdout_sha256": sha256(stdout_path),
        "stderr_path": str(stderr_path.relative_to(OUT)),
        "stderr_sha256": sha256(stderr_path),
        "python": sys.version.split()[0],
        "platform": sys.platform,
        "interpreter": sys.executable,
        "env_notes": {
            "TEMP": os.environ.get("TEMP"),
            "PYTHONPATH": os.environ.get("PYTHONPATH"),
        },
    }


attempts = []
for index in range(1, MAX_ATTEMPTS + 1):
    row = one_attempt(index)
    attempts.append(row)
    print(json.dumps(row, ensure_ascii=False), flush=True)
    if row["exit_code"] == 0:
        break

(OUT / "fast-entry-runs.json").write_text(
    json.dumps(attempts, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
sys.exit(0 if attempts[-1]["exit_code"] == 0 else 1)
