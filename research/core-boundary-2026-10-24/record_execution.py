"""Record a parent-observed process exit; does not infer exits from log text."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("phase",choices=["frontier","export"])
parser.add_argument("exit_code",type=int)
args = parser.parse_args()
path = OUT/"execution.json"
data = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
source = ROOT/"candidates/core-kummer"/("Boundary/Frontier.lean" if args.phase=="frontier" else "ExportFrontier.lean")
log = OUT/("frontier-build.log" if args.phase=="frontier" else "declarations.raw.json")
data[args.phase] = {"exit_code":args.exit_code,
    "recorded_at_utc":datetime.now(timezone.utc).isoformat(),
    "source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
    "output_sha256":hashlib.sha256(log.read_bytes()).hexdigest(),
    "basis":"Exit code returned by the parent execution tool, explicitly recorded by parent"}
path.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
print(f"recorded {args.phase} exit={args.exit_code}")
