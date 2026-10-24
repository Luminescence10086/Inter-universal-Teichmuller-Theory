"""Read-only audit of committed delivery objects; never executes delivery scripts."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
ROOT = Path(__file__).resolve().parents[2]
GIT = r"C:\Program Files\Git\cmd\git.exe"
DELIVERY = "53f6062edeb6563e0a5e357f558f51502eb94403"
PREFIX = "handoffs/round2-2026-10-23"

def git(*args, cwd=ROOT):
    return subprocess.check_output([GIT, "-C", str(cwd), *args])

def blob(path):
    return git("show", f"{DELIVERY}:{path.replace(chr(92), '/')}")

results = []
for task in ("p0", "e1", "e2", "e3", "m1", "m2"):
    base = f"{PREFIX}/{task}"
    bundle = json.loads(blob(f"{base}/bundle.json"))
    head = bundle["head_commit"]
    wt = ROOT / ".wt" / task
    actual_head = git("rev-parse", "HEAD", cwd=wt).decode().strip()
    changed = git("diff", "--name-only", bundle["base_commit"], head).decode().splitlines()
    scope_base = bundle.get("previous_head_commit", bundle["base_commit"])
    scoped_changed = ([] if bundle.get("verdict") == "no-change" else
        git("diff", "--name-only", scope_base, head).decode().splitlines())
    mismatches = []
    logs = bundle.get("logs", [])
    entries = []
    if isinstance(logs, list):
        entries += [(x["path"], x["sha256"], x.get("bytes")) for x in logs]
    elif isinstance(logs, dict):
        entries += [(f"logs/{p}", x["sha256"], x.get("bytes")) for p, x in logs.items()]
    entries += [(p, sha, None) for p, sha in bundle.get("log_sha256", {}).items()]
    for path, sha, size in entries:
        path = path.replace(chr(92), "/")
        data = blob(path if path.startswith(PREFIX + "/") else f"{base}/{path}")
        if hashlib.sha256(data).hexdigest() != sha.lower() or (size is not None and len(data) != size):
            mismatches.append(path)
    dirty_changed = []
    for path in changed:
        current = wt / path
        if not current.exists() or current.read_bytes() != git("show", f"{head}:{path}"):
            dirty_changed.append(path)
    declared = [x["path"] if isinstance(x, dict) else x for x in bundle["changed_paths"]]
    results.append(dict(task=task, head=head, head_matches=actual_head == head,
        changed_since_base=changed, scope_base=scope_base, scoped_changed_paths=scoped_changed,
        declared_paths_match=set(scoped_changed) == set(declared),
        checked_logs=len(entries), log_hash_mismatches=mismatches,
        worktree_source_mismatches=dirty_changed))
output = dict(delivery_commit=DELIVERY, tasks=results)
(Path(__file__).parent / "delivery-object-check.json").write_text(
    json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(output, ensure_ascii=False, indent=2))
if any(not x["head_matches"] or not x["declared_paths_match"] or
       x["log_hash_mismatches"] or x["worktree_source_mismatches"] for x in results):
    sys.exit(1)
