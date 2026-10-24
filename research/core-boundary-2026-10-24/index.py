"""Read-only query/check or regenerate the isolated formal dependency shard.

Never runs Lean or an editor. Saved execution and actual UI evidence are required
before admission. --check is freshness checking, not a replacement for Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
PROJECT = ROOT / "candidates/core-kummer"
SOURCE = PROJECT / "Boundary/Frontier.lean"
INDEX = OUT / "index.json"
SHARD = ROOT / "fact-tree/core-boundary-2026-10-24.json"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    return p.read_text(encoding="utf-8-sig")

def load(p):
    return json.loads(read(p))

def generate():
    execution = load(OUT/"execution.json")
    assert execution["frontier"]["exit_code"] == execution["export"]["exit_code"] == 0
    assert execution["frontier"]["source_sha256"] == sha(SOURCE)
    assert execution["frontier"]["output_sha256"] == sha(OUT/"frontier-build.log")
    assert execution["export"]["source_sha256"] == sha(PROJECT/"ExportFrontier.lean")
    assert execution["export"]["output_sha256"] == sha(OUT/"declarations.raw.json")
    assembly = load(OUT/"assembly.json")
    assert assembly["output_sha256"] == sha(SOURCE)
    assert all(sha(ROOT/p) == h for p,h in assembly["input_sha256"].items())
    log = read(OUT/"frontier-build.log")
    assert not re.search(r"\berror[:(]|\bwarning:", log), "diagnostics present"
    assert "sorryAx" not in log
    reports = {n: sorted(a.strip() for a in ax.split(",") if a.strip())
        for n, ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
    selected = set(re.findall(r"(?m)^#print axioms (\S+)\s*$",read(SOURCE)))
    assert set(reports) == selected, "missing or extra axiom reports"
    for name, axioms in reports.items():
        assert set(axioms) <= ALLOW, (name, axioms)
    raw_lines = read(OUT/"declarations.raw.json").splitlines()
    assert len(raw_lines) == 2 and raw_lines[1].startswith("UPSTREAM_EXTERNAL_DECLARATIONS=")
    rows = json.loads(raw_lines[0])
    upstream = json.loads(raw_lines[1].split("=",1)[1])
    assert [r["id"] for r in upstream] == ["KummerTheory.Decomposition.decompositionMap_surjective"]
    ids = {r["id"] for r in rows}
    assert len(ids) == len(rows)
    own = selected & ids
    assert selected-ids == {"KummerTheory.Decomposition.decompositionMap_surjective"}
    assert all(r["module"] == "Boundary.Frontier" for r in rows)
    edges = sorted({(d,r["id"]) for r in rows for d in r["constants"] if d in ids and d != r["id"]})
    adjacency = {n:[] for n in ids}
    for a,b in edges:
        adjacency[a].append(b)
    seen, active = set(), set()
    def visit(n):
        assert n not in active, "dependency cycle"
        if n in seen:
            return
        active.add(n)
        for nxt in adjacency[n]:
            visit(nxt)
        active.remove(n)
        seen.add(n)
    for n in ids:
        visit(n)
    observation_path = OUT/"editor/observation.json"
    observed = load(observation_path) if observation_path.exists() else None
    admitted = False
    if observed:
        assert observed["source_sha256"] == sha(SOURCE), "stale editor source"
        assert observed["information_messages"] == len(selected)
        assert observed["errors"] == observed["warnings"] == 0
        assert observed["last_message"] in read(OUT/"editor/final.txt")
        admitted = True
    for row in rows:
        row["axioms"] = reports.get(row["id"])
        row["selected"] = row["id"] in own
        row["external_boundary"] = sorted(set(row["constants"])-ids)
        row["source_file"] = SOURCE.relative_to(ROOT).as_posix()
    # Bind the actual local import closure, not unrelated future audit tools.
    local_sources = set()
    def include_source(path):
        if path in local_sources:
            return
        local_sources.add(path)
        for module in re.findall(r"(?m)^import\s+(\S+)\s*$",read(path)):
            dep = PROJECT/(module.replace(".","/")+".lean")
            if dep.is_file():
                include_source(dep)
    include_source(SOURCE)
    include_source(PROJECT/"ExportFrontier.lean")
    inputs = list(local_sources) + [ROOT/p for p in assembly["input_sha256"]]
    for source in local_sources:
        if source.name == "ExportFrontier.lean":
            continue
        artifact = PROJECT/".lake/build/lib/lean"/source.relative_to(PROJECT).with_suffix(".olean")
        assert artifact.is_file(), f"missing checked artifact: {artifact}"
        inputs.append(artifact)
        for suffix in (".private", ".server"):
            extra = Path(str(artifact)+suffix)
            if extra.exists():
                inputs.append(extra)
    inputs += [PROJECT/p for p in ["lean-toolchain","lakefile.lean","lake-manifest.json"]]
    inputs += [OUT/p for p in ["execution.json","frontier-build.log","declarations.raw.json",
        "external-declarations.log","assembly.json","port-manifest.json","upstream-port.patch"]]
    if observed:
        inputs += [observation_path]+list((OUT/"editor").glob("*.txt"))+list((OUT/"editor").glob("*.png"))
    result = {"schema":1,"shard_id":"core-boundary-2026-10-24",
        "status":"VERIFIED_LOCAL_SHARD" if admitted else "EDITOR_PENDING",
        "scope":"Discrete valuations, actual finite-place fields and conditional germ comparison; no original IUT gap closure",
        "selected_count":len(own),"graph_node_count":len(rows),"upstream_checks":sorted(selected-ids),
        "nodes":sorted(rows,key=lambda r:r["id"]),"external_declarations":upstream,
        "edges":[{"from":a,"to":b} for a,b in edges],
        "edge_semantics":"A -> B means B uses A in its type or proof",
        "axioms_allowed":sorted(ALLOW),"editor_observation":observed,
        "input_sha256":{p.relative_to(ROOT).as_posix():sha(p) for p in sorted(set(inputs))}}
    INDEX.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    if admitted:
        SHARD.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"selected":len(own),"nodes":len(rows),"edges":len(edges),"status":result["status"]}))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check",action="store_true")
parser.add_argument("--query")
args = parser.parse_args()
if args.check or args.query:
    data = load(INDEX)
    stale = [p for p,h in data["input_sha256"].items() if sha(ROOT/p) != h]
    assert not stale, f"stale verification inputs: {stale}"
    if args.query:
        matches = [n for n in data["nodes"] if args.query.casefold() in n["id"].casefold()]
        found = {n["id"] for n in matches}
        print(json.dumps({"matches":[{k:v for k,v in n.items() if k not in
            {"constants","external_boundary"}} for n in matches],
            "edges":[e for e in data["edges"] if e["from"] in found or e["to"] in found]},ensure_ascii=False,indent=2))
        sys.exit(0 if matches else 1)
    if data["status"] == "VERIFIED_LOCAL_SHARD":
        assert load(SHARD) == data, "shard/index differ"
    print(f"PASS: saved input hashes and shard/index match ({data['status']}); no Lean replay")
else:
    generate()
