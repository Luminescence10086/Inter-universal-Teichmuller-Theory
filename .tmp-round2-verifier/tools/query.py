"""Quick read-only access to the admitted theorem DAG."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("query", nargs="?", default="")
args = parser.parse_args()
tree = json.loads((root / "fact-tree/facts.json").read_text(encoding="utf-8"))
if tree.get("status") != "checked":
    raise SystemExit("fact-tree is not currently checked; run tools/verify.py")
for path, expected in tree.get("context_sha256", {}).items():
    if hashlib.sha256((root / path).read_bytes()).hexdigest() != expected:
        raise SystemExit("proof context changed; run tools/verify.py and renew the VS Code receipt")
for node in tree["nodes"]:
    current = hashlib.sha256((root / node["source"]).read_bytes()).hexdigest()
    if current != node["sha256"]:
        raise SystemExit("source changed; run tools/verify.py and renew the VS Code receipt")
for node in tree["nodes"]:
    if args.query.lower() in (node["id"] + " " + node["statement"]).lower():
        print(node["id"])
        print("  " + node["statement"].replace("\n", "\n  "))
        print("  dependencies: " + (", ".join(node["depends_on"]) or "none"))
        print("  axioms: " + (", ".join(node["axioms"]) or "none"))
