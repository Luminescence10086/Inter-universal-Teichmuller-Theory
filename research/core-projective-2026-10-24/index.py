"""Index the projective-comparison Lean export; never runs Lean or an editor."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
PROJECT = ROOT / "candidates/core-kummer"
SOURCE = PROJECT / "Boundary/ProjectiveComparison.lean"
EXPORTER = PROJECT / "ExportProjectiveComparison.lean"
EXECUTION = OUT / "execution.json"
BUILD_LOG = OUT / "lean-build.log"
EXPORT_STDERR = OUT / "export.stderr.log"
RAW = OUT / "declarations.raw.json"
EDITOR = OUT / "editor"
INDEX = OUT / "index.json"
SHARD = ROOT / "fact-tree/core-projective-2026-10-24.json"
PARENT_OUT = ROOT / "research/core-comparison-2026-10-24"
PARENT_INDEX = PARENT_OUT / "index.json"
PARENT_CHECK = PARENT_OUT / "index.py"
PARENT_SHARD = ROOT / "fact-tree/core-comparison-2026-10-24.json"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_MODULE = "Boundary.ProjectiveComparison"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return path.read_text(encoding="utf-8-sig")


def load(path):
    return json.loads(read(path))


def selected_names():
    return re.findall(r"(?m)^#print axioms (\S+)\s*$", read(SOURCE))


def import_closure(path, found=None):
    found = set() if found is None else found
    path = path.resolve()
    if path in found:
        return found
    found.add(path)
    for module in re.findall(r"(?m)^import\s+(\S+)\s*$", read(path)):
        dependency = PROJECT / (module.replace(".", "/") + ".lean")
        if dependency.is_file():
            import_closure(dependency, found)
    return found


def validate_axioms(log, selected):
    assert not re.search(r"\berror[:(]|\bwarning:", log), "Lean diagnostics present"
    assert "sorryAx" not in log, "sorryAx found"
    reports = {name: sorted(x.strip() for x in axioms.split(",") if x.strip())
               for name, axioms in re.findall(
                   r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
    assert set(reports) == set(selected), "axiom log does not exactly match #print list"
    for name, axioms in reports.items():
        assert set(axioms) <= ALLOW, (name, axioms)
    return reports


def check_acyclic(ids, edges):
    adjacency = {name: [] for name in ids}
    for edge in edges:
        adjacency[edge["from"]].append(edge["to"])
    visited, active = set(), set()

    def visit(name):
        assert name not in active, "dependency cycle"
        if name in visited:
            return
        active.add(name)
        for child in adjacency[name]:
            visit(child)
        active.remove(name)
        visited.add(name)

    for name in ids:
        visit(name)


def generate():
    # Verify the previous isolated shard first; its --check never invokes Lean.
    subprocess.run([sys.executable, str(PARENT_CHECK), "--check"], cwd=ROOT, check=True)
    parent = load(PARENT_INDEX)
    execution = load(EXECUTION)
    assert execution["build"]["exit_code"] == execution["export"]["exit_code"] == 0
    assert execution["build"]["source_sha256"] == sha(SOURCE)
    assert execution["build"]["output_sha256"] == sha(BUILD_LOG)
    assert execution["export"]["source_sha256"] == sha(EXPORTER)
    assert execution["export"]["output_sha256"] == sha(RAW)
    export_stderr = read(EXPORT_STDERR)
    assert not re.search(r"\berror[:(]|\bwarning:", export_stderr), "export diagnostics present"

    selected = selected_names()
    assert len(selected) == 9 and len(set(selected)) == 9
    build_log = read(BUILD_LOG)
    reports = validate_axioms(build_log, selected)
    raw_lines = read(RAW).splitlines()
    assert len(raw_lines) == 1, "expected one-line declaration JSON"
    rows = json.loads(raw_lines[0])
    assert isinstance(rows, list)
    ids = {row["id"] for row in rows}
    assert len(ids) == len(rows)
    assert set(selected) <= ids, "selected declarations missing from export rows"
    assert all(row["module"] == EXPECTED_MODULE for row in rows)

    edges = sorted({(dependency, row["id"]) for row in rows
                    for dependency in row["constants"] if dependency in ids
                    and dependency != row["id"]})
    edge_rows = [{"from": a, "to": b} for a, b in edges]
    check_acyclic(ids, edge_rows)
    ancestor_ids = set()
    ancestor_shards = []
    seen_shards = set()
    ancestor_path = PARENT_SHARD
    while True:
        ancestor_relpath = ancestor_path.relative_to(ROOT).as_posix()
        assert ancestor_relpath not in seen_shards, "parent_shard cycle"
        seen_shards.add(ancestor_relpath)
        ancestor_data = load(ancestor_path)
        ancestor_digest = sha(ancestor_path)
        ancestor_shards.append({"path": ancestor_relpath, "sha256": ancestor_digest})
        ancestor_ids.update(row["id"] for row in ancestor_data["nodes"])
        next_parent = ancestor_data.get("parent_shard")
        if next_parent is None:
            break
        assert sha(ROOT / next_parent["path"]) == next_parent["sha256"], \
            f"stale parent shard link: {next_parent['path']}"
        ancestor_path = ROOT / next_parent["path"]
    ancestor_fact_edges = sorted({(dependency, row["id"]) for row in rows
                                  for dependency in row["constants"]
                                  if dependency in ancestor_ids})
    ancestor_fact_edge_rows = [{"from": a, "to": b} for a, b in ancestor_fact_edges]

    observation_path = EDITOR / "observation.json"
    observed = load(observation_path) if observation_path.is_file() else None
    admitted = False
    if observed is not None:
        assert observed["source_sha256"] == sha(SOURCE), "stale editor observation"
        assert observed["information_messages"] == 9
        assert observed["errors"] == observed["warnings"] == 0
        assert observed["last_message"] in read(EDITOR / "final.txt")
        for evidence in ("all.txt", "all.png", "final.txt", "final.png"):
            assert (EDITOR / evidence).is_file(), f"missing editor evidence: {evidence}"
        admitted = True

    for row in rows:
        row["axioms"] = reports.get(row["id"])
        row["selected"] = row["id"] in set(selected)
        row["external_dependencies"] = sorted(set(row["constants"]) - ids)
        row["source_file"] = SOURCE.relative_to(ROOT).as_posix()

    # The parent index validates existing source/build hashes; bind this module's local
    # import closure and compiled artifacts as well.
    closure = import_closure(SOURCE)
    closure |= import_closure(EXPORTER)
    inputs = {ROOT / Path(path) for path in parent["input_sha256"]}
    inputs.update({PARENT_INDEX, PARENT_CHECK, PARENT_SHARD, Path(__file__).resolve()})
    inputs.update(ROOT / Path(shard["path"]) for shard in ancestor_shards)
    inputs |= closure
    for source in closure:
        if source.name == EXPORTER.name:
            continue
        artifact = PROJECT / ".lake/build/lib/lean" / source.relative_to(PROJECT).with_suffix(".olean")
        assert artifact.is_file(), f"missing local compiled artifact: {artifact}"
        inputs.add(artifact)
        for suffix in (".private", ".server"):
            extra = Path(str(artifact) + suffix)
            if extra.exists():
                inputs.add(extra)
    inputs.update({SOURCE, EXPORTER, EXECUTION, BUILD_LOG, EXPORT_STDERR, RAW})
    if observed is not None:
        inputs.add(observation_path)
        for pattern in ("all.txt", "all.png", "final.txt", "final.png"):
            inputs.update(EDITOR.glob(pattern))

    result = {
        "schema": 1,
        "shard_id": "core-projective-2026-10-24",
        "status": "VERIFIED_LOCAL_SHARD" if admitted else "CANDIDATE_ONLY",
        "scope": "Projective Kummer/valuation comparison lemmas; no original IUT gap closure",
        "selected_count": len(selected),
        "graph_node_count": len(rows),
        "nodes": sorted(rows, key=lambda row: row["id"]),
        "edges": edge_rows,
        "parent_shard": {
            "path": PARENT_SHARD.relative_to(ROOT).as_posix(),
            "sha256": sha(PARENT_SHARD),
        },
        "ancestor_shards": ancestor_shards,
        "ancestor_fact_edges": ancestor_fact_edge_rows,
        "edge_semantics": "A -> B means B uses A in its type or proof",
        "axioms_allowed": sorted(ALLOW),
        "editor_observation": observed,
        "input_sha256": {path.relative_to(ROOT).as_posix(): sha(path)
                         for path in sorted(inputs)},
    }
    INDEX.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if admitted:
        SHARD.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"selected": len(selected), "nodes": len(rows),
                      "edges": len(edge_rows), "status": result["status"]}))


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true", help="check saved index/shard hashes only")
parser.add_argument("--query", help="fuzzy declaration name; show exact type and dependencies")
args = parser.parse_args()
if args.check or args.query:
    data = load(INDEX)
    stale = [path for path, digest in data["input_sha256"].items()
             if sha(ROOT / path) != digest]
    assert not stale, f"stale index inputs: {stale}"
    if args.query:
        matches = [row for row in data["nodes"]
                   if args.query.casefold() in row["id"].casefold()]
        print(json.dumps({"matches": matches}, ensure_ascii=False, indent=2))
        sys.exit(0 if matches else 1)
    if data["status"] == "VERIFIED_LOCAL_SHARD":
        assert load(SHARD) == data, "saved shard/index differ"
    print(f"PASS: saved input hashes and shard/index match ({data['status']}); no Lean replay")
else:
    generate()
