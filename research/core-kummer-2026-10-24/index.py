"""Index Lean-exported statements and A -> B proof dependencies; no Lean execution."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
FILES = {
    "KummerValuationSeparation": "candidates/core-local-global/KummerValuationSeparation.lean",
    "KummerClassValuationBridge": "candidates/core-kummer/KummerClassValuationBridge.lean",
    "CohomologyReflection": "candidates/core-kummer/CohomologyReflection.lean",
}
ALLOW = {"propext", "Classical.choice", "Quot.sound"}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def generate():
    log = (OUT / "core-kummer-build.log").read_text(encoding="utf-8-sig")
    assert "Build completed successfully" in log
    assert not re.search(r"(?m)^(?:error|warning):", log)
    assert "sorryAx" not in log
    reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log))
    rows = json.loads((OUT / "declarations.raw.log").read_text(encoding="utf-8-sig"))
    ids = {r["id"] for r in rows}
    assert len(ids) == len(rows)
    selected = set()
    for path in FILES.values():
        selected.update(re.findall(r"(?m)^#print axioms (\S+)\s*$",
            (ROOT / path).read_text(encoding="utf-8-sig")))
    assert len(selected) == 25 and selected <= reports.keys()
    own = selected & ids
    assert len(own) == 23
    for name, ax in reports.items():
        assert set(x.strip() for x in ax.split(",") if x.strip()) <= ALLOW, name
    for row in rows:
        assert set(row["axioms"]) <= ALLOW, row["id"]
        row["source_file"] = FILES[row["module"]]
        row["selected"] = row["id"] in own
        row["external_boundary"] = sorted(set(row["constants"]) - ids)
    edges = sorted({(dep, r["id"]) for r in rows for dep in r["constants"]
                    if dep in ids and dep != r["id"]})
    observations = OUT / "editor" / "observations.json"
    observed = json.loads(observations.read_text(encoding="utf-8")) if observations.exists() else {}
    clean_modules = set()
    for entry in observed.get("files", []):
        module = Path(entry["file"]).stem
        if module not in FILES:
            continue
        assert entry["sha256"] == digest(ROOT / FILES[module]), "stale editor source"
        expected_count = sum(1 for name in selected if name in reports and
            f"'{name}' depends on axioms:" in log and
            name in re.findall(r"(?m)^#print axioms (\S+)\s*$",
                (ROOT / FILES[module]).read_text(encoding="utf-8-sig")))
        assert entry["informationMessages"] == expected_count
        assert entry["errors"] == entry["warnings"] == 0
        assert entry["lastMessage"] in (OUT / "editor" / entry["finalTree"]).read_text(encoding="utf-8")
        clean_modules.add(module)
    inputs = [ROOT / f for f in FILES.values()] + [OUT / "core-kummer-build.log",
        OUT / "declarations.raw.log"] + list((ROOT / "candidates/core-kummer").glob("*.lean"))
    inputs += list((ROOT / "candidates/core-kummer/ContinuousKummerTheory").rglob("*.lean"))
    inputs += [ROOT / "candidates/core-kummer/lake-manifest.json", ROOT / "candidates/core-kummer/lean-toolchain"]
    if observations.exists():
        inputs += [observations] + list((OUT/"editor").glob("*.txt")) + list((OUT/"editor").glob("*.png"))
    result = {"schema": 1, "selected_local_count": len(own),
        "upstream_checks": sorted(selected - ids), "kernel_constant_count": len(rows),
        "edge_semantics": "A -> B means B directly depends on A in its type or proof",
        "nodes": sorted(rows, key=lambda x: x["id"]),
        "edges": [{"from": a, "to": b} for a, b in edges],
        "editor_observations": observed,
        "admission": "CANDIDATE_INDEX_ONLY; central registry unchanged",
        "input_sha256": {p.relative_to(ROOT).as_posix(): digest(p) for p in set(inputs)}}
    (OUT / "candidate-index.json").write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n",encoding="utf-8")
    if clean_modules == set(FILES):
        adjacency = {n: [] for n in ids}
        for a, b in edges:
            adjacency[a].append(b)
        visited, active = set(), set()
        def visit(n):
            assert n not in active, "dependency cycle"
            if n in visited:
                return
            active.add(n)
            for child in adjacency[n]:
                visit(child)
            active.remove(n)
            visited.add(n)
        for n in ids:
            visit(n)
        shard = {**result, "shard_id": "core-kummer-2026-10-24",
            "admission": "VERIFIED_LOCAL_SHARD", "graph_acyclic": True,
            "scope": "Conditional Qp Kummer/valuation tools and generic H1 reflection; no original IUT gap closed"}
        (ROOT/"fact-tree/core-kummer-2026-10-24.json").write_text(
            json.dumps(shard, ensure_ascii=False, indent=2)+"\n",encoding="utf-8")
        print("verified local fact-tree shard: 23 nodes; central registry unchanged")
    print(json.dumps({k:result[k] for k in ("selected_local_count", "upstream_checks", "kernel_constant_count", "admission")},ensure_ascii=False))
    print(f"dependency edges: {len(edges)}")
    changes = []
    source = OUT / "continuous-kummer-pin/ContinuousKummerTheory"
    target = ROOT / "candidates/core-kummer/ContinuousKummerTheory"
    for dest in sorted(target.rglob("*.lean")):
        rel = dest.relative_to(target)
        changes.extend(difflib.unified_diff((source/rel).read_text(encoding="utf-8").splitlines(True),
            dest.read_text(encoding="utf-8-sig").splitlines(True), fromfile=f"upstream/{rel.as_posix()}",tofile=f"ported/{rel.as_posix()}"))
    (OUT / "upstream-port.patch").write_text("".join(changes),encoding="utf-8")

parser = argparse.ArgumentParser()
parser.add_argument("--query")
parser.add_argument("--check", action="store_true")
args = parser.parse_args()
if args.query or args.check:
    data = json.loads((OUT/"candidate-index.json").read_text(encoding="utf-8"))
    stale = [p for p, h in data["input_sha256"].items() if digest(ROOT/p) != h]
    assert not stale, f"stale inputs: {stale}"
    if args.query:
        matches = [n for n in data["nodes"] if args.query.casefold() in n["id"].casefold()]
        found = {n["id"] for n in matches}
        print(json.dumps({"matches":matches,"edges":[e for e in data["edges"]
              if e["from"] in found or e["to"] in found]},ensure_ascii=False,indent=2))
        sys.exit(0 if matches else 1)
    shard_path = ROOT / "fact-tree/core-kummer-2026-10-24.json"
    if shard_path.exists():
        shard = json.loads(shard_path.read_text(encoding="utf-8"))
        assert shard["input_sha256"] == data["input_sha256"]
        assert shard["nodes"] == data["nodes"] and shard["edges"] == data["edges"]
        assert shard["admission"] == "VERIFIED_LOCAL_SHARD"
        print("input hashes match; isolated verified shard matches index")
    else:
        print("input hashes match; candidate index only")
else:
    generate()
