"""Read-only package preflight. Never executes deliveries, Lean, or UI actions.

PACKAGE_COMPLETE describes recorded material, not verified mathematics.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import re
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
HEX = re.compile(r"[0-9a-f]{64}\Z")
STATUSES = {"RESEARCH_ONLY", "NO_RESULT_WITH_GAP", "CLI_CANDIDATE", "EDITOR_CANDIDATE"}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"), object_pairs_hook=unique_object)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local_file(root, value):
    require(isinstance(value, str) and value, "file path must be a nonempty string")
    # Bundle paths are relative and portable. Resolve also rejects escaping symlinks.
    require(not re.match(r"^[A-Za-z]:", value) and not value.startswith(("/", "\\")),
            f"bundle file must be relative: {value}")
    path = (root / value.replace("\\", "/")).resolve()
    require(path.is_relative_to(root.resolve()), f"path escapes delivery: {value}")
    require(path.is_file(), f"missing file: {value}")
    return path


def catalog_check(folder):
    baseline = read_json(folder / "baseline.json")
    catalog = read_json(folder / "tasks.json")
    rows = catalog["tasks"]
    require(catalog["count"] == len(rows) == 128, "expected 128 tasks")
    tasks = {r["id"]: r for r in rows}
    require(set(tasks) == {f"T{i:03d}" for i in range(1, 129)}, "task ID mismatch")
    baseline_sha = digest(folder / "baseline.json")
    visited, active = set(), set()

    def visit(ident):
        if ident in visited:
            return
        require(ident not in active, f"dependency cycle: {ident}")
        active.add(ident)
        for dep in tasks[ident]["dependencies"]:
            require(dep in tasks, f"unknown dependency: {dep}")
            visit(dep)
        active.remove(ident)
        visited.add(ident)

    for row in rows:
        require(row["baseline_sha256"] == baseline_sha, f"baseline mismatch: {row['id']}")
        require(digest(local_file(folder, row["card"])) == row["card_sha256"],
                f"card SHA mismatch: {row['id']}")
        visit(row["id"])
    seed = read_json(folder / "source-seed.json")
    seed_path = local_file(folder, seed["path"])
    require(digest(seed_path) == seed["sha256"], "source seed SHA mismatch")
    with zipfile.ZipFile(seed_path) as archive:
        files = baseline["files"]
        names = [e["path"] for e in files]
        require(len(names) == len(set(names)), "duplicate baseline input")
        require(set(archive.namelist()) == set(names), "seed input list mismatch")
        for entry in files:
            require(hashlib.sha256(archive.read(entry["path"])).hexdigest() == entry["sha256"],
                    f"seed bytes mismatch: {entry['path']}")
    return tasks, baseline


def delivery_check(path, tasks):
    root = path.resolve().parent
    data = read_json(path)
    require(data.get("schema_version") == 1, "unsupported schema_version")
    ident = data.get("task_id")
    require(ident in tasks, "unknown task_id")
    task = tasks[ident]
    require(data.get("task_card_sha256") == task["card_sha256"], "task card SHA mismatch")
    require(data.get("baseline_sha256") == task["baseline_sha256"], "baseline SHA mismatch")
    status = data.get("status")
    require(status in STATUSES, "invalid status")
    artifacts = data.get("artifacts")
    require(isinstance(artifacts, list) and artifacts, "artifacts required")
    known = {}
    for item in artifacts:
        p = local_file(root, item["path"])
        key = str(p).casefold()
        require(key not in known, f"duplicate artifact: {item['path']}")
        actual_sha = item.get("sha256", "")
        require(isinstance(actual_sha, str) and HEX.fullmatch(actual_sha), "invalid artifact SHA")
        require(digest(p) == actual_sha, f"artifact SHA mismatch: {item['path']}")
        require(isinstance(item.get("role"), str) and item["role"], "artifact role required")
        known[key] = item

    def registered(value):
        p = local_file(root, value)
        require(str(p).casefold() in known, f"unhashed artifact: {value}")
        return known[str(p).casefold()]

    registered(data.get("summary_file"))
    registered(data.get("replay_file"))
    if status == "NO_RESULT_WITH_GAP":
        registered(data.get("gap_file"))
    runs = data.get("runs", [])
    require(isinstance(runs, list), "runs must be a list")
    bound_sources = set()
    for run in runs:
        require(isinstance(run.get("argv"), list) and run["argv"] and
                all(isinstance(a, str) for a in run["argv"]), "run argv required")
        require(isinstance(run.get("cwd"), str) and run["cwd"], "run cwd required")
        require(type(run.get("exit_code")) is int, "actual run exit_code required")
        duration = run.get("duration_seconds")
        require(type(duration) in (int, float) and math.isfinite(duration) and duration >= 0,
                "actual duration required")
        registered(run.get("stdout"))
        registered(run.get("stderr"))
        for source in run.get("inputs", []):
            entry = registered(source["path"])
            require(source.get("sha256") == entry["sha256"], "run input SHA mismatch")
            if run.get("kind") == "lean":
                bound_sources.add(entry["sha256"])
        # A recorded run either supports the delivery or is explicitly kept as a
        # discarded attempt / negative control. Anything else with a nonzero exit
        # is a failure laundered into the package, whatever the reported status.
        # Before this rule the check only fired for CLI/EDITOR candidates, so a
        # RESEARCH_ONLY package could carry exit_code:1 runs and still pass
        # (red-team finding: 8/8 bypasses across four real deliveries).
        keep_as_negative = (
            run.get("discarded_attempt") is True
            or run.get("negative_control") is True
            or run.get("kind") in {"discarded_attempt", "negative_control"}
        )
        if keep_as_negative:
            continue
        require(run["exit_code"] == 0,
                "recorded run has a nonzero exit and is not marked discarded_attempt/negative_control")
        # The stored stdout/stderr must exist, otherwise "exit 0" is unbacked.
        # Empty stderr is legitimate; empty stdout on a Lean run is not.
        stdout_entry = registered(run.get("stdout"))
        stdout_path = local_file(root, stdout_entry["path"])
        if run.get("kind") == "lean":
            require(stdout_path.stat().st_size > 0,
                    "Lean run recorded an empty stdout; exit 0 is not evidenced")
    declarations = data.get("declarations", [])
    require(isinstance(declarations, list), "declarations must be a list")

    # Axiom hygiene. The protocol forbids sorry, admit and ad-hoc axioms, but the
    # checker never looked. The red team assembled a PACKAGE_COMPLETE delivery
    # whose own logs contained three "declaration uses sorry" lines and twelve
    # sorryAx occurrences, using T049's untouched evidence. Any axioms log that
    # mentions sorryAx, or any declaration whose axioms list escapes the accepted
    # whitelist, now fails here.
    ACCEPTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
    for decl in declarations:
        log_entry = registered(decl.get("axioms_log"))
        log_path = local_file(root, log_entry["path"])
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        require("sorryAx" not in log_text,
                f"axioms log contains sorryAx for {decl.get('name')}")
        declared_axioms = decl.get("axioms")
        if isinstance(declared_axioms, list):
            extra = {a for a in declared_axioms if a not in ACCEPTED_AXIOMS}
            require(not extra,
                    f"declaration {decl.get('name')} depends on axioms outside the "
                    f"accepted set: {sorted(extra)}")

    for decl in declarations:
        require(isinstance(decl.get("name"), str) and decl["name"], "declaration name required")
        require(isinstance(decl.get("type"), str) and decl["type"] and
                "REPLACE_WITH" not in decl["type"], "complete actual Lean type required")
        entry = registered(decl["source_file"])
        require(entry["sha256"] == decl.get("source_sha256"), "declaration source SHA mismatch")
        require(isinstance(decl.get("direct_dependencies"), list), "direct dependencies required")
        registered(decl.get("axioms_log"))
        if status in {"CLI_CANDIDATE", "EDITOR_CANDIDATE"}:
            require(entry["sha256"] in bound_sources, "declaration not bound to a recorded Lean run")
    if status in {"CLI_CANDIDATE", "EDITOR_CANDIDATE"} and task["proof_mode"] == "LEAN_CANDIDATE":
        require(declarations and any(r.get("kind") == "lean" for r in runs),
                "Lean candidate lacks declarations or recorded Lean runs")
        require(any("-DwarningAsError=true" in r["argv"] for r in runs if r.get("kind") == "lean"),
                "strict Lean command not recorded")
    deps = data.get("dependency_deliveries", [])
    require(isinstance(deps, list), "dependency_deliveries must be a list")
    for dep in deps:
        require(dep.get("task_id") in task["dependencies"], "unexpected task dependency receipt")
        entry = registered(dep.get("path"))
        require(dep.get("sha256") == entry["sha256"], "dependency receipt SHA mismatch")
    if status in {"CLI_CANDIDATE", "EDITOR_CANDIDATE"}:
        require({d["task_id"] for d in deps} == set(task["dependencies"]),
                "candidate lacks dependency delivery records")
    if status == "EDITOR_CANDIDATE":
        editor = data.get("editor", {})
        require(editor.get("performed") is True, "editor performed flag missing")
        registered(editor.get("evidence_file"))
        require(editor.get("source_sha256") in {d["source_sha256"] for d in declarations},
                "editor evidence source SHA not bound")
    return {"result": "PACKAGE_COMPLETE", "task_id": ident, "reported_status": status,
            "scope": "Material and hashes only. No reported command executed; mathematics, axioms, source semantics and editor observations remain unverified."}


def self_test(tasks):
    # Synthetic research-only fixture. These are not Lean/editor receipts.
    with tempfile.TemporaryDirectory(prefix="iut-delivery-preflight-") as temp:
        root = Path(temp)
        for name, content in {"SUMMARY.md": "Synthetic fixture; no research performed.\n",
                              "replay.py": "# synthetic, never executed\n"}.items():
            (root / name).write_text(content, encoding="utf-8")
        task = tasks["T001"]
        sample = {"schema_version": 1, "task_id": "T001", "status": "RESEARCH_ONLY",
                  "task_card_sha256": task["card_sha256"], "baseline_sha256": task["baseline_sha256"],
                  "summary_file": "SUMMARY.md", "replay_file": "replay.py", "runs": [],
                  "declarations": [], "dependency_deliveries": [],
                  "artifacts": [{"path": n, "sha256": digest(root / n), "role": "fixture"}
                                for n in ["SUMMARY.md", "replay.py"]]}
        path = root / "delivery.json"

        def save(value):
            path.write_text(json.dumps(value), encoding="utf-8")

        save(sample)
        delivery_check(path, tasks)
        negatives = []
        for mode in ["bad_hash", "missing_file", "stale_card", "escape_path", "false_lean_candidate"]:
            mutated = json.loads(json.dumps(sample))
            if mode == "bad_hash":
                mutated["artifacts"][0]["sha256"] = "0" * 64
            elif mode == "missing_file":
                mutated["summary_file"] = "absent.md"
            elif mode == "stale_card":
                mutated["task_card_sha256"] = "0" * 64
            elif mode == "escape_path":
                mutated["summary_file"] = "../outside.md"
            else:
                t = tasks["T017"]
                mutated.update(task_id="T017", task_card_sha256=t["card_sha256"], status="CLI_CANDIDATE")
            save(mutated)
            try:
                delivery_check(path, tasks)
            except (ValueError, KeyError):
                negatives.append(mode)
            else:
                raise ValueError(f"negative fixture accepted: {mode}")
    return {"result": "PREFLIGHT_SELF_TEST_OK", "synthetic_positive": 1,
            "synthetic_rejections": negatives, "Lean_or_editor_executed": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--delivery", type=Path)
    parser.add_argument("--catalog", type=Path, default=HERE)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--check-catalog", action="store_true")
    args = parser.parse_args()
    try:
        tasks, _ = catalog_check(args.catalog.resolve())
        if args.self_test:
            result = self_test(tasks)
        elif args.delivery:
            result = delivery_check(args.delivery.resolve(), tasks)
        else:
            result = {"result": "CATALOG_COMPLETE", "tasks": len(tasks),
                      "scope": "128 cards, dependency DAG, baseline and source-seed hashes only."}
        print(json.dumps(result, ensure_ascii=False))
        return 0
    except (ValueError, KeyError, TypeError, OSError, zipfile.BadZipFile) as error:
        print(json.dumps({"result": "PACKAGE_INCOMPLETE", "error": str(error)}, ensure_ascii=False))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
