"""Record exact upstream inputs and current port deltas. Does not execute Lean."""
from pathlib import Path
import difflib
import hashlib
import json

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
records = json.loads((OUT/"source-files.json").read_text(encoding="utf-8-sig"))["files"]
patch, result = [], []
for record in records:
    source_root = (ROOT/"research/core-kummer-2026-10-24/continuous-kummer-pin"
        if record["sourceRepository"] == "continuous-kummer-pin" else
        ROOT/"reviews/core-round/external/continuous-kummer-theory")
    source = source_root/record["sourceRelativePath"]
    target = ROOT/record["targetRelativePath"]
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    assert source_hash == record["sourceSha256"], "upstream source drift"
    changes = list(difflib.unified_diff(source.read_text(encoding="utf-8-sig").splitlines(True),
        target.read_text(encoding="utf-8-sig").splitlines(True),
        fromfile="upstream/"+record["sourceRelativePath"],tofile=record["targetRelativePath"]))
    patch.extend(changes)
    result.append({"path":record["targetRelativePath"],"upstream_commit":record["sourceCommit"],
        "upstream_sha256":source_hash,"current_sha256":hashlib.sha256(target.read_bytes()).hexdigest(),
        "text_changed":bool(changes)})
(OUT/"upstream-port.patch").write_text("".join(patch),encoding="utf-8")
(OUT/"port-manifest.json").write_text(json.dumps({"note":"Current port bytes; initial copy receipts remain in source-files.json",
    "files":result},indent=2)+"\n",encoding="utf-8")
print(f"recorded {len(result)} modules, {sum(x['text_changed'] for x in result)} changed")
