#!/usr/bin/env python3
"""E2 regression: a production snapshot *membership* change must never read as intact.

The bug (review ``reviews/4841271-acceptance/REVIEW.md`` R3/P2): ``audit/affected.py``
only matched keys that already existed in the old receipt / ``checked-inputs.json``.  The
real verifiers glob their input sets (``IUTBridge/**/*.lean``, ``tools/*.py``,
``.vscode/*.json``), so a file that appeared after the observation changes the real input
map while appearing in no recorded key -- and the planner still said ``void=false``,
``nodes_to_pending=0``.

Every fixture below is an isolated, miniature copy of the real three-project workspace in
``tempfile.TemporaryDirectory()``.  The verifier files are *copied* from this repository
and the receipts are filled with the output of those very functions, so each case
exercises the production rules

    bridge/tools/verify_integrated.py : project_snapshot / dependency_snapshot
    tools/verify.py                   : snapshot
    local-field/tools/verify.py       : snapshot

and never a re-implementation of them.  Each case first proves the premise independently
(the production function really gains/loses a member, or really refuses to run) and then
asserts what the planner reports.

Run one acceptance case (this is the frozen argv contract):

    python -B audit/tests/test_affected_snapshot_membership.py E2.new_lean_glob_member

Exit status: ``0`` the case (or every listed case) held, ``1`` it failed, ``2`` unknown
case id, ``3`` the case skipped itself because this checkout cannot answer it (never a
silent pass).  Without arguments the whole file runs under unittest, as before.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TOOL = Path(__file__).resolve().parents[1] / "affected.py"
REPO = Path(__file__).resolve().parents[2]

VERIFIER_FILES = {
    "main": "tools/verify.py",
    "local": "local-field/tools/verify.py",
    "bridge": "bridge/tools/verify_integrated.py",
}

#: Admitted-node counts of the real receipts (main 38, local 24, bridge 73).
ADMITTED = {"main": 38, "local": 24, "bridge": 73}
TOTAL_ADMITTED = sum(ADMITTED.values())  # 135

#: Source files backing the admitted nodes of each project (project-relative).
NODE_SOURCES = {
    "main": ["IUTAudit/Core.lean", "IUTAudit/Dep.lean", "IUTAudit/Claim.lean"],
    "local": ["LocalFieldAudit/Base.lean", "LocalFieldAudit/Shell.lean"],
    "bridge": ["IUTBridge/Admissibility.lean", "IUTBridge/Integration.lean"],
}

COMMIT_ENV = {
    "GIT_AUTHOR_NAME": "fixture",
    "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
    "GIT_COMMITTER_NAME": "fixture",
    "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
    "GIT_CONFIG_NOSYSTEM": "1",
}


# --------------------------------------------------------------------------------------
# fixture files
# --------------------------------------------------------------------------------------
def write_text(path: Path, text: str = "-- fixture\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")


def copy_verifier(root: Path, project: str) -> None:
    target = root / VERIFIER_FILES[project]
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(REPO / VERIFIER_FILES[project], target)


def facts_for(project: str) -> dict:
    sources = NODE_SOURCES[project]
    nodes = []
    for index in range(ADMITTED[project]):
        source = sources[index % len(sources)]
        module = source.removesuffix(".lean").replace("/", ".")
        nodes.append({
            "id": f"{module}.n{index}",
            "module": module,
            "source": source,
            "status": "admitted",
            "depends_on": [],
        })
    # One dependency edge, so a source change also has a transitive dependent.
    nodes[1]["depends_on"] = [nodes[0]["id"]]
    return {
        "nodes": nodes,
        "edges": [{"from": nodes[0]["id"], "to": nodes[1]["id"]}],
    }


def build_fixture(root: Path) -> None:
    """Create the miniature workspace, then record it with the production functions."""
    # --- root project ("main") -----------------------------------------------------
    write_text(root / "README.md", "# fixture repository\n")
    write_text(root / "research/notes.md", "# research notes\n")
    write_text(root / "audit/extra_probe.py", "# a code file no verifier snapshot reads\n")
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "IUTAudit.lean",
                 "IUTAudit/Core.lean", "IUTAudit/Dep.lean", "IUTAudit/Claim.lean",
                 "tools/query.py", "tools/Export.lean", "tools/Imports.lean",
                 "tools/EditorCheck.lean"):
        write_text(root / name)
    write_json(root / "tools/catalog.json", [])
    write_json(root / ".vscode/settings.json", {"editor.formatOnSave": True})

    # --- local-field ---------------------------------------------------------------
    for name in ("local-field/lean-toolchain", "local-field/lakefile.toml",
                 "local-field/LocalFieldAudit.lean",
                 "local-field/LocalFieldAudit/Base.lean",
                 "local-field/LocalFieldAudit/Shell.lean",
                 "local-field/tools/query.py", "local-field/tools/Export.lean",
                 "local-field/tools/Imports.lean", "local-field/tools/EditorCheck.lean"):
        write_text(root / name)
    write_json(root / "local-field/lake-manifest.json", {"packages": []})
    write_json(root / "local-field/external-lock.json", {"schema": 1, "packages": []})
    write_json(root / "local-field/tools/catalog.json", [])
    write_json(root / "local-field/.vscode/settings.json", {"editor.formatOnSave": True})

    # --- bridge --------------------------------------------------------------------
    for name in ("bridge/lean-toolchain", "bridge/lakefile.toml", "bridge/lake-manifest.json",
                 "bridge/IUTBridge.lean",
                 "bridge/IUTBridge/Admissibility.lean",
                 "bridge/IUTBridge/Integration.lean",
                 "bridge/staging/Candidate.lean"):
        write_text(root / name)
    write_json(root / "bridge/tools/catalog.json", [])
    write_json(root / "bridge/.vscode/settings.json", {"editor.formatOnSave": True})

    # --- the production verifiers themselves (copied, never re-implemented) --------
    for project in VERIFIER_FILES:
        copy_verifier(root, project)

    # --- fact trees ----------------------------------------------------------------
    for project, rel in (("main", ""), ("local", "local-field"), ("bridge", "bridge")):
        base = root / rel if rel else root
        write_json(base / "fact-tree/facts.json", facts_for(project))

    # --- record the observation with the production snapshot functions -------------
    inputs = {project: production_input_set(root, project) for project in VERIFIER_FILES}
    dependencies = production_dependency_set(root)
    for project, rel in (("main", ""), ("local", "local-field"), ("bridge", "bridge")):
        base = root / rel if rel else root
        schema = 3 if project == "bridge" else 2
        targets = sorted(node["id"] for node in facts_for(project)["nodes"])
        record = {
            "schema": schema,
            "input_sha256": inputs[project],
            "checked_targets": targets,
            "evidence": "verification/observation.txt",
            "evidence_sha256": "0" * 64,
        }
        if project == "bridge":
            record["dependency_sha256"] = dependencies
        write_json(base / "verification/vscode-receipt.json", record)
        checked = {
            "schema": schema,
            "input_sha256": inputs[project],
            "checked_targets": targets,
        }
        if project == "bridge":
            checked["dependency_sha256"] = dependencies
        write_json(base / "verification/checked-inputs.json", checked)
        write_text(base / "verification/observation.txt", "editor observation\n")

    # --- one cross-project contract, recorded twice --------------------------------
    abstract = {"project": "main", "theorem": "IUTAudit.Core.n0"}
    concrete = {"project": "bridge", "theorem": "IUTBridge.Admissibility.n0"}
    write_json(root / "bridges/contracts.json", {
        "schema": 1,
        "contracts": [{"id": "BR-01", "kind": "instantiation",
                       "abstract": abstract, "concrete": [concrete]}],
    })
    write_json(root / "bridges/facts.json", {
        "schema": 1,
        "projects": {"main": ".", "local": "local-field", "bridge": "bridge"},
        "contracts": [{"id": "BR-01", "kind": "instantiation", "status": "checked",
                       "abstract": abstract, "concrete": ["IUTBridge.Admissibility.n0"]}],
    })
    write_json(root / "bridges/statement-lock.json", {"schema": 1, "projects": {}})
    write_json(root / "bridges/integrated-lock.json", {"schema": 2, "entries": {}})


# --------------------------------------------------------------------------------------
# the production snapshot functions, loaded out of the fixture itself
# --------------------------------------------------------------------------------------
def load_fixture_verifier(root: Path, project: str):
    path = root / VERIFIER_FILES[project]
    spec = importlib.util.spec_from_file_location(
        f"e2_fixture_{project}_{abs(hash(str(root)))}", path)
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise AssertionError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def production_input_set(root: Path, project: str) -> dict:
    """The project's real input map, computed by the project's own verifier."""
    module = load_fixture_verifier(root, project)
    function = getattr(module, "project_snapshot", None)
    if function is None:
        function = module.snapshot
    try:
        return function(root / ("bridge" if project == "bridge" else
                                "local-field" if project == "local" else "."))
    except TypeError:  # pragma: no cover - snapshot() takes no argument
        return function()


def production_dependency_set(root: Path) -> dict:
    """The bridge verifier's cross-project input map (schema-3 ``dependency_sha256``)."""
    module = load_fixture_verifier(root, "bridge")
    return module.dependency_snapshot(module.DEP)


# --------------------------------------------------------------------------------------
# case machinery
# --------------------------------------------------------------------------------------
CASES: dict[str, type] = {}


def case(case_id: str):
    def register(cls):
        cls.CASE_ID = case_id
        CASES[case_id] = cls
        return cls
    return register


def git(root: Path, *args: str) -> str:
    env = dict(os.environ, **COMMIT_ENV)
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed: {proc.stderr}")
    return proc.stdout


class MembershipCase(unittest.TestCase):
    """One isolated miniature workspace per case."""

    CASE_ID = ""
    maxDiff = None

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name) / "repo"
        build_fixture(self.root)
        git(self.root, "init", "-q", "-b", "main")
        git(self.root, "config", "core.autocrlf", "false")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "fixture: recorded observation")

    # -- running the planner ---------------------------------------------------------
    def run_tool(self, *args: str, expect: int = 0) -> subprocess.CompletedProcess:
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        proc = subprocess.run(
            [sys.executable, "-B", str(TOOL), "--repo", str(self.root), *args],
            capture_output=True, text=True, encoding="utf-8", env=env, cwd=str(REPO),
        )
        self.assertEqual(
            proc.returncode, expect,
            msg=f"unexpected exit {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
        )
        return proc

    def payload(self, *args: str) -> dict:
        return json.loads(self.run_tool(*args, "--json").stdout)

    @staticmethod
    def receipts(payload: dict) -> dict:
        return {row["project"]: row for row in payload["receipts"]}

    def commit(self, message: str) -> None:
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", message)

    # -- the production rules, asked directly ----------------------------------------
    def input_keys(self, project: str) -> set[str]:
        return set(production_input_set(self.root, project))

    def dependency_keys(self) -> set[str]:
        return set(production_dependency_set(self.root))

    def is_live_member(self, project: str, repo_path: str) -> bool:
        """Is ``repo_path`` a member of the project's real input map?

        The key conventions are the verifiers' own: project-relative, ``@workspace/``
        for the workspace root, absolute paths for ``dependency_sha256``.
        """
        if project == "main":
            return repo_path in self.input_keys("main")
        if project == "local":
            prefix = "local-field/"
            return (repo_path[len(prefix):] in self.input_keys("local")
                    if repo_path.startswith(prefix) else False)
        if repo_path.startswith("bridge/"):
            return repo_path[len("bridge/"):] in self.input_keys("bridge")
        return f"@workspace/{repo_path}" in self.input_keys("bridge")

    def is_dependency_member(self, repo_path: str) -> bool:
        target = (self.root / repo_path).resolve()
        for key in self.dependency_keys():
            try:
                if Path(key).resolve() == target:
                    return True
            except OSError:  # pragma: no cover - unreadable absolute pin
                continue
        return False

    # -- assertions ------------------------------------------------------------------
    def assert_status(self, payload: dict, project: str, expected: str,
                      decided: bool | None = None) -> None:
        row = self.receipts(payload)[project]
        self.assertEqual(
            row["status"], expected,
            msg=f"{project} should be {expected}, got {row['status']}:\n"
                + json.dumps(row, indent=1, ensure_ascii=False),
        )
        self.assertEqual(row["void"], expected == "VOID")
        must_decide = decided if decided is not None else expected == "INTACT"
        if must_decide:
            self.assertEqual(
                row["membership"]["probe"]["input"]["status"], "decided",
                msg="this case must be decided by the production snapshot function",
            )

    def assert_added_member(self, payload: dict, project: str, repo_path: str,
                            origin: str = "input") -> None:
        added = self.receipts(payload)[project]["membership"]["added"]
        self.assertIn(
            {"path": repo_path, "origin": origin}, added,
            msg=f"{project} membership additions were {added}",
        )

    def human_flag(self, text: str, payload: dict, project: str) -> str:
        target = self.receipts(payload)[project]["path"]
        for line in text.splitlines():
            stripped = line.strip()
            tokens = stripped.split()
            if (tokens and tokens[0] in ("VOID", "INTACT", "UNKNOWN")
                    and target in tokens):
                return tokens[0]
        self.fail(f"no receipt line for {project} in:\n{text}")
    # NB: no test method here; every case subclass defines ``test_case`` so that
    # unittest discovery does not pick up this base class.


# --------------------------------------------------------------------------------------
# E2.new_lean_glob_member -- a new IUTBridge/**/*.lean member, comment-only, unimported
# --------------------------------------------------------------------------------------
@case("E2.new_lean_glob_member")
class TestNewLeanGlobMember(MembershipCase):
    def test_case(self) -> None:
        added_path = "bridge/IUTBridge/NewCandidate.lean"
        before = self.input_keys("bridge")
        write_text(self.root / added_path, "-- comment only; nothing imports this file\n")
        after = self.input_keys("bridge")
        # Premise, from the production function: the real input map changed.
        self.assertNotEqual(before, after)
        self.assertIn("IUTBridge/NewCandidate.lean", after)
        self.assertNotIn("IUTBridge/NewCandidate.lean", before)

        payload = self.payload("--files", added_path)
        self.assert_status(payload, "bridge", "VOID")          # the bug said INTACT
        self.assert_added_member(payload, "bridge", added_path, "input")
        bridge = self.receipts(payload)["bridge"]
        self.assertTrue(bridge["void"])
        self.assertEqual(bridge["nodes_to_pending"], ADMITTED["bridge"])
        self.assertEqual(bridge["membership"]["added"], [{"path": added_path, "origin": "input"}])
        # The other two projects do not glob bridge/IUTBridge/**.
        self.assert_status(payload, "main", "INTACT")
        self.assert_status(payload, "local", "INTACT")
        self.assertEqual(payload["counts"]["receipts_voided"], 1)
        self.assertEqual(payload["counts"]["receipts_unknown"], 0)
        self.assertEqual(payload["counts"]["snapshot_members_added"], 1)
        self.assertEqual(payload["counts"]["nodes_to_pending"], ADMITTED["bridge"])
        # A file no node claims: it is still unpinned, but no longer harmless.
        self.assertIn(added_path, payload["unpinned"])
        self.assertFalse(self.is_live_member("main", added_path))
        self.assertFalse(self.is_live_member("local", added_path))
        # Human output must not call the bridge receipt intact.
        text = self.run_tool("--files", added_path).stdout
        self.assertEqual(self.human_flag(text, payload, "bridge"), "VOID")
        self.assertEqual(self.human_flag(text, payload, "main"), "INTACT")


# --------------------------------------------------------------------------------------
# E2.new_workspace_tool -- a new root tools/ file the bridge snapshot globs
# --------------------------------------------------------------------------------------
@case("E2.new_workspace_tool")
class TestNewWorkspaceTool(MembershipCase):
    def test_case(self) -> None:
        added_path = "tools/e2_workspace_probe.py"
        before = {project: self.input_keys(project) for project in VERIFIER_FILES}
        write_text(self.root / added_path, "# new workspace tool, no consumer yet\n")
        after = {project: self.input_keys(project) for project in VERIFIER_FILES}
        self.assertIn("@workspace/tools/e2_workspace_probe.py", after["bridge"])
        self.assertNotIn("@workspace/tools/e2_workspace_probe.py", before["bridge"])
        self.assertTrue(self.is_live_member("bridge", added_path))

        payload = self.payload("--files", added_path)
        self.assert_status(payload, "bridge", "VOID")
        self.assert_added_member(payload, "bridge", added_path, "input")
        self.assertEqual(self.receipts(payload)["bridge"]["nodes_to_pending"],
                         ADMITTED["bridge"])
        # The root verifier hashes a fixed tool list, so this is not a main member.
        self.assertFalse(self.is_live_member("main", added_path))
        self.assert_status(payload, "main", "INTACT")
        self.assert_status(payload, "local", "INTACT")
        self.assertEqual(payload["counts"]["receipts_voided"], 1)
        self.assertEqual(after["main"], before["main"])
        self.assertEqual(after["local"], before["local"])


# --------------------------------------------------------------------------------------
# E2.new_vscode_config -- a new .vscode/*.json member
# --------------------------------------------------------------------------------------
@case("E2.new_vscode_config")
class TestNewVscodeConfig(MembershipCase):
    def test_case(self) -> None:
        added_path = ".vscode/tasks.json"
        write_json(self.root / added_path, {"version": "2.0.0", "tasks": []})
        self.assertIn(".vscode/tasks.json", self.input_keys("main"))
        self.assertIn("@workspace/.vscode/tasks.json", self.input_keys("bridge"))
        self.assertTrue(self.is_live_member("main", added_path))
        self.assertTrue(self.is_live_member("bridge", added_path))

        payload = self.payload("--files", added_path)
        self.assert_status(payload, "main", "VOID")
        self.assert_status(payload, "bridge", "VOID")
        self.assert_added_member(payload, "main", added_path, "input")
        self.assert_added_member(payload, "bridge", added_path, "input")
        self.assertEqual(self.receipts(payload)["main"]["nodes_to_pending"],
                         ADMITTED["main"])
        self.assertEqual(self.receipts(payload)["bridge"]["nodes_to_pending"],
                         ADMITTED["bridge"])
        self.assertEqual(payload["counts"]["receipts_voided"], 2)
        self.assertEqual(payload["counts"]["nodes_to_pending"],
                         ADMITTED["main"] + ADMITTED["bridge"])
        # local-field keeps its own .vscode directory.
        self.assertFalse(self.is_live_member("local", added_path))
        self.assert_status(payload, "local", "INTACT")


# --------------------------------------------------------------------------------------
# E2.rename_into_scope -- out-of-rule file renamed into a globbed directory
# --------------------------------------------------------------------------------------
@case("E2.rename_into_scope")
class TestRenameIntoScope(MembershipCase):
    def test_case(self) -> None:
        source = "bridge/staging/Candidate.lean"
        target = "bridge/IUTBridge/Candidate.lean"
        self.assertFalse(self.is_live_member("bridge", source))
        git(self.root, "mv", source, target)
        self.commit("move candidate into the snapshot rule")
        self.assertTrue(self.is_live_member("bridge", target))
        self.assertFalse(self.is_live_member("bridge", source))

        payload = self.payload("--range", "HEAD~1..HEAD")
        paths = [row["path"] for row in payload["changed"]]
        self.assertIn(source, paths)
        self.assertIn(target, paths)
        self.assert_status(payload, "bridge", "VOID")
        self.assert_added_member(payload, "bridge", target, "input")
        added = self.receipts(payload)["bridge"]["membership"]["added"]
        self.assertEqual([item["path"] for item in added], [target])
        self.assertEqual(payload["counts"]["receipts_voided"], 1)
        self.assert_status(payload, "main", "INTACT")
        self.assert_status(payload, "local", "INTACT")


# --------------------------------------------------------------------------------------
# E2.rename_out_of_scope -- in-rule file renamed out of every rule
# --------------------------------------------------------------------------------------
@case("E2.rename_out_of_scope")
class TestRenameOutOfScope(MembershipCase):
    def test_case(self) -> None:
        source = "bridge/IUTBridge/Admissibility.lean"
        target = "bridge/staging/Admissibility.lean"
        self.assertTrue(self.is_live_member("bridge", source))
        git(self.root, "mv", source, target)
        self.commit("move an admitted source out of the snapshot rule")
        self.assertFalse(self.is_live_member("bridge", source))
        self.assertFalse(self.is_live_member("bridge", target))

        payload = self.payload("--range", "HEAD~1..HEAD")
        paths = [row["path"] for row in payload["changed"]]
        self.assertIn(source, paths)
        self.assertIn(target, paths)
        bridge = self.receipts(payload)["bridge"]
        self.assert_status(payload, "bridge", "VOID")
        # Decided by the recorded pin, not by a membership guess: the old key is gone.
        self.assertTrue(bridge["pins"])
        self.assertEqual([pin["key"] for pin in bridge["pins"]], ["IUTBridge/Admissibility.lean"])
        self.assertEqual(bridge["membership"]["added"], [])
        # The moved file also carried admitted statements.
        self.assertIn("IUTBridge.Admissibility.n0", payload["theorems"]["invalidated"])
        self.assertEqual(payload["counts"]["receipts_voided"], 1)
        self.assert_status(payload, "main", "INTACT")
        self.assert_status(payload, "local", "INTACT")


# --------------------------------------------------------------------------------------
# E2.delete_pinned_input -- a recorded input disappears
# --------------------------------------------------------------------------------------
@case("E2.delete_pinned_input")
class TestDeletePinnedInput(MembershipCase):
    def test_case(self) -> None:
        removed = "local-field/LocalFieldAudit/Base.lean"
        self.assertTrue(self.is_live_member("local", removed))
        self.assertTrue(self.is_dependency_member(removed))
        git(self.root, "rm", "-q", removed)
        self.commit("delete a pinned dependency input")
        self.assertFalse(self.is_live_member("local", removed))

        payload = self.payload("--range", "HEAD~1..HEAD")
        self.assert_status(payload, "local", "VOID")
        self.assert_status(payload, "bridge", "VOID")
        self.assert_status(payload, "main", "INTACT")
        local = self.receipts(payload)["local"]
        bridge = self.receipts(payload)["bridge"]
        self.assertEqual(local["nodes_to_pending"], ADMITTED["local"])
        self.assertEqual(bridge["nodes_to_pending"], ADMITTED["bridge"])
        self.assertEqual([pin["kind"] for pin in bridge["pins"]], ["dependency"])
        self.assertEqual(payload["counts"]["nodes_to_pending"],
                         ADMITTED["local"] + ADMITTED["bridge"])
        self.assertEqual(payload["counts"]["receipts_unknown"], 0)

        # A deletion that makes a hard-coded snapshot input disappear must still be a
        # definite "not intact", and the planner must survive the snapshot raising.
        hard_coded = "tools/query.py"
        self.assertTrue(self.is_live_member("main", hard_coded))
        git(self.root, "rm", "-q", hard_coded)
        self.commit("delete a hard-coded root snapshot input")
        with self.assertRaises(FileNotFoundError):
            production_input_set(self.root, "main")
        second = self.payload("--range", "HEAD~1..HEAD")
        main = self.receipts(second)["main"]
        self.assert_status(second, "main", "VOID")
        self.assertEqual(main["membership"]["probe"]["input"]["status"], "unavailable")
        self.assertTrue(main["membership"]["probe"]["input"]["error"])
        self.assertTrue(main["membership"]["probe"]["input"]["error"].startswith("FileNotFoundError"))


# --------------------------------------------------------------------------------------
# E2.documentation_control -- prose must not invalidate machine evidence
# --------------------------------------------------------------------------------------
@case("E2.documentation_control")
class TestDocumentationControl(MembershipCase):
    def test_case(self) -> None:
        changed = "research/notes.md"
        new_doc = "research/new-notes.md"
        write_text(self.root / changed, "# research notes, edited\n")
        write_text(self.root / new_doc, "# more prose\n")
        for path in (changed, new_doc, "README.md"):
            for project in VERIFIER_FILES:
                self.assertFalse(self.is_live_member(project, path),
                                 msg=f"{path} must not be a snapshot input of {project}")
            self.assertFalse(self.is_dependency_member(path))

        payload = self.payload("--files", changed, new_doc, "README.md")
        for project in VERIFIER_FILES:
            self.assert_status(payload, project, "INTACT")
        self.assertEqual(payload["changed"][0]["classes"], ["documentation"])
        self.assertEqual(sorted(payload["docs"]), ["README.md", new_doc, changed])
        self.assertEqual(payload["counts"]["receipts_voided"], 0)
        self.assertEqual(payload["counts"]["receipts_unknown"], 0)
        self.assertEqual(payload["counts"]["snapshot_members_added"], 0)
        self.assertEqual(payload["counts"]["nodes_invalidated"], 0)
        self.assertEqual(payload["counts"]["nodes_to_pending"], 0)
        self.assertFalse(any("re-run" in step or "re-verify" in step for step in payload["redo"]))
        text = self.run_tool("--files", changed, new_doc, "README.md").stdout
        for project in VERIFIER_FILES:
            self.assertEqual(self.human_flag(text, payload, project), "INTACT")


# --------------------------------------------------------------------------------------
# E2.out_of_scope_control -- a code file outside every snapshot rule
# --------------------------------------------------------------------------------------
@case("E2.out_of_scope_control")
class TestOutOfScopeControl(MembershipCase):
    def test_case(self) -> None:
        changed = "audit/extra_probe.py"
        write_text(self.root / changed, "# still outside every verifier snapshot rule\n")
        for project in VERIFIER_FILES:
            self.assertFalse(self.is_live_member(project, changed))
        self.assertFalse(self.is_dependency_member(changed))

        payload = self.payload("--files", changed)
        for project in VERIFIER_FILES:
            self.assert_status(payload, project, "INTACT")
        # Not documentation either: this is a machine-code file that no rule covers.
        self.assertEqual(payload["changed"][0]["classes"], ["unpinned"])
        self.assertEqual(payload["docs"], [])
        self.assertEqual(payload["counts"]["receipts_voided"], 0)
        self.assertEqual(payload["counts"]["receipts_unknown"], 0)
        self.assertEqual(payload["counts"]["snapshot_members_added"], 0)
        self.assertEqual(payload["counts"]["nodes_invalidated"], 0)
        self.assertEqual(payload["counts"]["nodes_to_pending"], 0)
        self.assertEqual(payload["changed"][0]["snapshot_member_of"], [])
        text = self.run_tool("--files", changed).stdout
        for project in VERIFIER_FILES:
            self.assertEqual(self.human_flag(text, payload, project), "INTACT")


# --------------------------------------------------------------------------------------
# E2.distinct_node_counts -- invalidated and pending are separate ledgers
# --------------------------------------------------------------------------------------
@case("E2.distinct_node_counts")
class TestDistinctNodeCounts(MembershipCase):
    def test_case(self) -> None:
        payload = self.payload(
            "--files", "tools/verify.py", "local-field/tools/verify.py",
            "bridge/IUTBridge/Admissibility.lean",
        )
        for project in VERIFIER_FILES:
            self.assert_status(payload, project, "VOID")
            self.assertEqual(
                self.receipts(payload)[project]["admitted_at_observation"],
                ADMITTED[project],
            )
            self.assertEqual(
                self.receipts(payload)[project]["nodes_to_pending"],
                ADMITTED[project],
            )
        counts = payload["counts"]
        self.assertEqual(counts["receipts_voided"], 3)
        self.assertEqual(counts["nodes_total"], TOTAL_ADMITTED)
        # 38 + 24 + 73, not the bridge-only 73.
        self.assertEqual(counts["nodes_to_pending"], TOTAL_ADMITTED)
        self.assertNotEqual(counts["nodes_to_pending"], ADMITTED["bridge"])
        self.assertEqual(counts["nodes_to_pending"],
                         sum(row["nodes_to_pending"] for row in payload["receipts"]))
        # The other ledger counts invalidated statements, not pending admissions.
        self.assertEqual(counts["nodes_invalidated"], len(payload["theorems"]["invalidated"]))
        self.assertNotEqual(counts["nodes_invalidated"], counts["nodes_to_pending"])
        self.assertEqual(
            counts["nodes_invalidated"],
            counts["nodes_direct"] + counts["nodes_transitive_dependents"],
        )
        hand = payload["hand_reconstruction"]["counts"]
        self.assertEqual(hand["nodes_invalidated"], counts["nodes_invalidated"])
        self.assertEqual(hand["nodes_to_pending"], counts["nodes_to_pending"])
        text = self.run_tool(
            "--files", "tools/verify.py", "local-field/tools/verify.py",
            "bridge/IUTBridge/Admissibility.lean",
        ).stdout
        self.assertIn(
            f"{counts['nodes_invalidated']} invalidated, {TOTAL_ADMITTED} -> pending", text)


# --------------------------------------------------------------------------------------
# extra (not a frozen case id): undecidable membership is UNKNOWN, never INTACT
# --------------------------------------------------------------------------------------
@case("E2.extra.membership_unavailable_unknown")
class TestMembershipUnavailable(MembershipCase):
    def test_case(self) -> None:
        # Replace the verifiers with modules that expose no snapshot function at all.
        for project, target in VERIFIER_FILES.items():
            write_text(self.root / target, "#!/usr/bin/env python3\nNO_SNAPSHOT = True\n")
        payload = self.payload("--files", "README.md")
        for project in VERIFIER_FILES:
            row = self.receipts(payload)[project]
            self.assertEqual(row["status"], "UNKNOWN",
                             msg=f"{project} must be UNKNOWN, not {row['status']}")
            self.assertFalse(row["void"])
            self.assertEqual(row["nodes_to_pending"], 0)
            self.assertEqual(row["membership"]["probe"]["input"]["status"], "unavailable")
            self.assertTrue(row["not_intact_because"])
        self.assertEqual(payload["counts"]["receipts_unknown"], 3)
        self.assertEqual(payload["counts"]["receipts_voided"], 0)
        self.assertEqual(payload["counts"]["nodes_to_pending"], 0)
        text = self.run_tool("--files", "README.md").stdout
        for project in VERIFIER_FILES:
            self.assertEqual(self.human_flag(text, payload, project), "UNKNOWN")
        self.assertNotIn("INTACT", text)

        # The opt-out switch must fail closed: it can never produce a definite INTACT.
        disabled = self.payload("--files", "README.md", "--no-membership-probe")
        for project in VERIFIER_FILES:
            self.assertEqual(self.receipts(disabled)[project]["status"], "UNKNOWN")
        self.assertEqual(disabled["snapshot_membership"]["probe"], "disabled")
        self.assertEqual(disabled["counts"]["receipts_unknown"], 3)


# --------------------------------------------------------------------------------------
# extra (not a frozen case id): the reviewer's own reproduction, on the real repository
# --------------------------------------------------------------------------------------
class RealRepoCase(unittest.TestCase):
    """Cases that read this checkout's real receipts instead of a fixture."""

    maxDiff = None

    def setUp(self) -> None:
        receipts = [REPO / rel for rel in (
            "verification/vscode-receipt.json",
            "local-field/verification/vscode-receipt.json",
            "bridge/verification/vscode-receipt.json",
        )]
        if not all(path.is_file() for path in receipts):
            self.skipTest("this checkout has no recorded receipts")
        for verifier in VERIFIER_FILES.values():
            if not (REPO / verifier).is_file():
                self.skipTest(f"missing production verifier {verifier}")

    def run_tool(self, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        proc = subprocess.run(
            [sys.executable, "-B", str(TOOL), *args],
            capture_output=True, text=True, encoding="utf-8", env=env, cwd=str(REPO),
        )
        self.assertEqual(proc.returncode, 0,
                         msg=f"exit {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}")
        return proc

    def payload(self, *args: str) -> dict:
        return json.loads(self.run_tool(*args, "--json").stdout)


@case("E2.extra.real_repo_new_glob_member")
class TestRealRepoNewGlobMember(RealRepoCase):
    def test_case(self) -> None:
        added = REPO / "bridge/IUTBridge/NewCandidate.lean"
        self.assertFalse(added.exists(),
                         msg="refusing to overwrite an existing file in the real checkout")
        before = set(production_input_set(REPO, "bridge"))
        added.write_text("-- new glob member, no theorem claimed\n", encoding="utf-8")
        self.addCleanup(lambda: added.unlink(missing_ok=True))
        after = set(production_input_set(REPO, "bridge"))
        # The reviewer's reproduction premise, recomputed with the production function.
        self.assertNotEqual(before, after)
        self.assertEqual(sorted(after - before), ["IUTBridge/NewCandidate.lean"])

        payload = self.payload("--files", "bridge/IUTBridge/NewCandidate.lean", "--json")
        rows = {row["project"]: row for row in payload["receipts"]}
        self.assertEqual(rows["bridge"]["status"], "VOID")
        self.assertTrue(rows["bridge"]["void"])
        self.assertEqual(rows["bridge"]["membership"]["added"],
                         [{"path": "bridge/IUTBridge/NewCandidate.lean", "origin": "input"}])
        self.assertEqual(rows["bridge"]["nodes_to_pending"],
                         rows["bridge"]["admitted_at_observation"])
        self.assertEqual(rows["local"]["status"], "INTACT")
        self.assertEqual(rows["main"]["status"], "INTACT")
        self.assertEqual(payload["counts"]["nodes_to_pending"],
                         rows["bridge"]["admitted_at_observation"])
        self.assertEqual(payload["counts"]["receipts_voided"], 1)


@case("E2.extra.review_range_replay")
class TestReviewRangeReplay(RealRepoCase):
    """The reviewer's frozen table row for ``--range 78bc059..4841271``."""

    def test_case(self) -> None:
        # Both endpoints are pinned commits, so the numbers below depend only on them.
        for revision in ("78bc059", "4841271"):
            probe = subprocess.run(["git", "-C", str(REPO), "cat-file", "-e", revision],
                                   capture_output=True)
            if probe.returncode != 0:
                self.skipTest(f"revision {revision} is not available")
        payload = self.payload("--range", "78bc059..4841271", "--json")
        counts = payload["counts"]
        self.assertEqual(counts["files"], 400)
        self.assertEqual(counts["receipts_voided"], 3)
        self.assertEqual(counts["receipts_unknown"], 0)
        self.assertEqual(counts["nodes_total"], 135)
        self.assertEqual(counts["nodes_invalidated"], 73)
        self.assertEqual(counts["nodes_to_pending"], 135)
        self.assertEqual(counts["contracts_invalidated"], 10)
        rows = {row["project"]: row for row in payload["receipts"]}
        self.assertEqual((rows["main"]["nodes_to_pending"],
                          rows["local"]["nodes_to_pending"],
                          rows["bridge"]["nodes_to_pending"]), (38, 24, 73))
        # 73 is the invalidated ledger; 73 is not the pending total.
        self.assertNotIn(73, (counts["nodes_to_pending"],))
        self.assertNotEqual(counts["nodes_invalidated"], counts["nodes_to_pending"])


# --------------------------------------------------------------------------------------
# runner: one case per invocation, exit 0 only when it holds
# --------------------------------------------------------------------------------------
def run_cases(case_ids: list[str]) -> int:
    """0 = every listed case held, 1 = a case failed, 3 = a case was skipped."""
    failed = 0
    skipped = 0
    for case_id in case_ids:
        suite = unittest.TestSuite([CASES[case_id]("test_case")])
        result = unittest.TextTestRunner(verbosity=2, stream=sys.stderr).run(suite)
        if result.failures or result.errors:
            failed += 1
            print(f"CASE {case_id}: FAIL")
        elif result.skipped:
            skipped += 1
            reason = "; ".join(text.strip() for _, text in result.skipped)
            print(f"CASE {case_id}: SKIP ({reason})")
        else:
            print(f"CASE {case_id}: PASS")
    if failed:
        return 1
    return 3 if skipped else 0


def main(argv: list[str]) -> int:
    if not argv:
        unittest.main(module=__name__, verbosity=2)
        return 0
    if argv[0] in ("--list", "-l"):
        for case_id in sorted(CASES):
            print(case_id)
        return 0
    unknown = [item for item in argv if item not in CASES]
    if unknown:
        print(f"unknown case id(s): {', '.join(unknown)}", file=sys.stderr)
        print("known case ids:\n  " + "\n  ".join(sorted(CASES)), file=sys.stderr)
        return 2
    return run_cases(argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
