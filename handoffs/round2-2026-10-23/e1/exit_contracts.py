"""Two exit-contract checks for the supervised entry, measured independently.

1. the supervisor relays a nonzero child status (`raise SystemExit(7)` -> 7);
2. a recorded-probe file is only reused for the same repository bytes: a forged
   witness must make the CLI refuse (exit 2) instead of reporting a verdict.
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

WT = Path("D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\.wt\\e1")
sys.path.insert(0, str(WT / "audit"))
sys.path.insert(0, str(WT / "audit" / "tests"))

import test_mutation_probe_exit as t

results = {}

code = t._relay(t._supervise([sys.executable, "-B", "-c", "raise SystemExit(7)"], 30.0),
                "probe-compound", 30.0)
results["relayed_child_exit_7"] = code

forged = Path(tempfile.mkdtemp(prefix="e1_forged_")) / "probes.json"
forged.write_text(json.dumps({"repo_witness": "0" * 64,
                              "probes": {"unpin_entry": {"ok": True, "detail": "forged"}}}),
                  encoding="utf-8")
proc = subprocess.run([sys.executable, "-B", str(WT / "audit" / "mutation_harness.py"),
                       "--json", "--probes-only", "--reuse-probes", str(forged)],
                      cwd=str(WT), capture_output=True, text=True,
                      encoding="utf-8", errors="replace", timeout=120)
results["forged_witness_exit"] = proc.returncode
results["forged_witness_stderr"] = proc.stderr.strip().splitlines()[-1:] or [""]
print(json.dumps(results, indent=2))
sys.exit(0 if (results["relayed_child_exit_7"] == 7
               and results["forged_witness_exit"] == 2) else 1)
