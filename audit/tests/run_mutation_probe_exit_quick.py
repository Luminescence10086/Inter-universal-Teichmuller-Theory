"""Run the E1 contract cases with a real total timeout and tree cleanup.

The baseline runs the complete M1-M8 matrix once. The remaining cases use the
same probe checks without repeating that matrix. On Windows, taskkill /T is run
while the owned Python runner is still alive so inherited-pipe grandchildren are
reaped before this entry point returns.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEST = ROOT / "audit/tests/test_mutation_probe_exit.py"
TOTAL_TIMEOUT_SECONDS = 270


def main() -> int:
    process = subprocess.Popen(
        [sys.executable, "-B", str(TEST)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", errors="replace",
    )
    try:
        stdout, stderr = process.communicate(timeout=TOTAL_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        if sys.platform == "win32":
            try:
                subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                               capture_output=True, timeout=5)
            except (OSError, subprocess.TimeoutExpired):
                pass
        else:
            process.kill()
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            stdout, stderr = process.communicate()
        sys.stdout.write(stdout)
        sys.stderr.write(stderr)
        print(f"INCOMPLETE: E1 quick replay exceeded total {TOTAL_TIMEOUT_SECONDS}s",
              file=sys.stderr)
        return 124
    sys.stdout.write(stdout)
    sys.stderr.write(stderr)
    print(f"E1 quick replay exited {process.returncode}")
    return process.returncode


if __name__ == "__main__":
    raise SystemExit(main())
