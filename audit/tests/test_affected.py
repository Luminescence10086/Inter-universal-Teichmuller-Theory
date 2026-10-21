#!/usr/bin/env python3
"""Tests for audit/affected.py.

Each test builds a throw-away git repository in ``tempfile.TemporaryDirectory()`` whose
recorded evidence mirrors the real repository's shape (three projects on two
toolchains, one schema-3 receipt with ``@workspace/`` pins and a cross-project
``dependency_sha256`` pin, one fact tree with ``depends_on`` + ``edges``, and one
cross-project contract with abstract/concrete/vendored endpoints).  The tool is then
run as a subprocess exactly as a reviewer would run it.

Run with:  python -m unittest discover -s audit/tests -v
       or: python audit/tests/test_affected.py
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "affected.py"
#: The production verifiers.  The fixture copies them instead of writing stubs so the
#: snapshot-membership probe in ``affected.py`` exercises the real snapshot functions.
REPO = Path(__file__).resolve().parents[2]
PRODUCTION_VERIFIERS = {
    "main": REPO / "tools/verify.py",
    "local": REPO / "local-field/tools/verify.py",
    "bridge": REPO / "bridge/tools/verify_integrated.py",
}

SHA = lambda char: (char * 64)
COMMIT_ENV = {
    "GIT_AUTHOR_NAME": "fixture",
    "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
    "GIT_COMMITTER_NAME": "fixture",
    "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
    "GIT_CONFIG_NOSYSTEM": "1",
}


# --------------------------------------------------------------------------------------
# fixture repository
# --------------------------------------------------------------------------------------
def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")


def write_text(path: Path, text: str = "placeholder\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def copy_verifier(root: Path, project: str, target: str) -> None:
    """Install a *production* verifier into the fixture (no re-implementation)."""
    destination = root / target
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PRODUCTION_VERIFIERS[project], destination)


def main_facts() -> dict:
    nodes = [
        {
            "id": "IUTAudit.Core.a", "module": "IUTAudit.Core", "source": "IUTAudit/Core.lean",
            "status": "admitted", "depends_on": [],
        },
        {
            "id": "IUTAudit.Dep.derived", "module": "IUTAudit.Dep", "source": "IUTAudit/Dep.lean",
            "status": "admitted", "depends_on": ["IUTAudit.Core.a"],
        },
        {
            "id": "IUTAudit.Claim.main", "module": "IUTAudit.Claim", "source": "IUTAudit/Claim.lean",
            "status": "admitted", "depends_on": [],
        },
    ]
    return {
        "nodes": nodes,
        "edges": [{"from": "IUTAudit.Core.a", "to": "IUTAudit.Dep.derived"}],
    }


def bridge_facts() -> dict:
    nodes = [
        {
            "id": "IUTBridge.Adm.t1", "module": "IUTBridge.Adm", "source": "IUTBridge/Adm.lean",
            "status": "admitted", "depends_on": [],
        },
        {
            "id": "IUTBridge.Adm.rect", "module": "IUTBridge.Adm", "source": "IUTBridge/Adm.lean",
            "status": "admitted", "depends_on": ["IUTBridge.Adm.t1"],
        },
        {
            "id": "IUTBridge.Integ.u1", "module": "IUTBridge.Integ", "source": "IUTBridge/Integ.lean",
            "status": "admitted", "depends_on": ["IUTBridge.Adm.rect"],
        },
    ]
    return {
        "nodes": nodes,
        "edges": [
            {"from": "IUTBridge.Adm.t1", "to": "IUTBridge.Adm.rect"},
            {"from": "IUTBridge.Adm.rect", "to": "IUTBridge.Integ.u1"},
        ],
    }


def local_facts() -> dict:
    nodes = [
        {
            "id": "LocalFieldAudit.Base.lx", "module": "LocalFieldAudit.Base",
            "source": "LocalFieldAudit/Base.lean", "status": "admitted", "depends_on": [],
        },
        {
            "id": "LocalFieldAudit.Base.ly", "module": "LocalFieldAudit.Base",
            "source": "LocalFieldAudit/Base.lean", "status": "admitted",
            "depends_on": ["LocalFieldAudit.Base.lx"],
        },
    ]
    return {"nodes": nodes, "edges": [{"from": "LocalFieldAudit.Base.lx", "to": "LocalFieldAudit.Base.ly"}]}


def build_fixture(root: Path) -> None:
    """Create a miniature but structurally faithful verification repository."""
    main_inputs = {
        "lean-toolchain": SHA("0"),
        "lakefile.toml": SHA("1"),
        "IUTAudit.lean": SHA("2"),
        "IUTAudit/Core.lean": SHA("3"),
        "IUTAudit/Dep.lean": SHA("4"),
        "IUTAudit/Claim.lean": SHA("b"),
        "tools/verify.py": SHA("5"),
        "tools/catalog.json": SHA("6"),
    }
    main_targets = ["IUTAudit.Claim.main", "IUTAudit.Core.a", "IUTAudit.Dep.derived"]
    write_json(root / "verification/checked-inputs.json", {
        "schema": 2, "input_sha256": main_inputs, "checked_targets": main_targets,
    })
    write_json(root / "verification/vscode-receipt.json", {
        "schema": 2, "evidence": "verification/obs.txt", "evidence_sha256": SHA("7"),
        "input_sha256": main_inputs, "checked_targets": main_targets,
    })
    write_text(root / "verification/obs.txt", "editor observation\n")
    write_json(root / "fact-tree/facts.json", main_facts())
    write_json(root / "tools/catalog.json", [
        {"id": "IUTAudit.Core.a", "source": "IUTAudit/Core.lean"},
        {"id": "IUTAudit.Dep.derived", "source": "IUTAudit/Dep.lean"},
        {"id": "IUTAudit.Claim.main", "source": "IUTAudit/Claim.lean"},
    ])
    write_text(root / "tools/helper.py", "# unpinned by main, pinned by bridge\n")
    # Production verifier plus the fixed inputs its own snapshot() hashes (a missing one
    # would make the membership probe undecidable, which is covered by the dedicated
    # snapshot-membership test file, not here).
    copy_verifier(root, "main", "tools/verify.py")
    for name in ("tools/query.py", "tools/Export.lean", "tools/Imports.lean",
                 "tools/EditorCheck.lean"):
        write_text(root / name)
    write_text(root / "lake-manifest.json", "{}\n")
    write_text(root / "IUTAudit.lean")
    write_text(root / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
    write_text(root / "lakefile.toml")
    write_text(root / "IUTAudit/Core.lean")
    write_text(root / "IUTAudit/Dep.lean")
    write_text(root / "IUTAudit/Claim.lean")
    write_text(root / "README.md", "# fixture\n")
    write_text(root / "research/notes.md", "# notes\n")

    # local-field: its own receipt, also pinned by bridge as a dependency
    local_inputs = {
        "lean-toolchain": SHA("8"),
        "LocalFieldAudit/Base.lean": SHA("9"),
        "tools/verify.py": SHA("a"),
        "tools/catalog.json": SHA("b"),
    }
    local_targets = ["LocalFieldAudit.Base.lx", "LocalFieldAudit.Base.ly"]
    write_json(root / "local-field/verification/checked-inputs.json", {
        "schema": 2, "input_sha256": local_inputs, "checked_targets": local_targets,
    })
    write_json(root / "local-field/verification/vscode-receipt.json", {
        "schema": 2, "evidence": "verification/obs-local.txt", "evidence_sha256": SHA("c"),
        "input_sha256": local_inputs, "checked_targets": local_targets,
    })
    write_text(root / "local-field/verification/obs-local.txt", "editor observation\n")
    write_json(root / "local-field/fact-tree/facts.json", local_facts())
    write_json(root / "local-field/tools/catalog.json", [
        {"id": "LocalFieldAudit.Base.lx", "source": "LocalFieldAudit/Base.lean"},
        {"id": "LocalFieldAudit.Base.ly", "source": "LocalFieldAudit/Base.lean"},
    ])
    write_text(root / "local-field/LocalFieldAudit/Base.lean")
    write_text(root / "local-field/lean-toolchain", "leanprover/lean4:v4.34.0-rc2\n")
    copy_verifier(root, "local", "local-field/tools/verify.py")
    for name in ("local-field/lakefile.toml", "local-field/LocalFieldAudit.lean",
                 "local-field/tools/query.py", "local-field/tools/Export.lean",
                 "local-field/tools/Imports.lean", "local-field/tools/EditorCheck.lean"):
        write_text(root / name)
    # bridge's dependency snapshot parses these two: real (empty) package lists.
    write_json(root / "local-field/lake-manifest.json", {"packages": []})
    write_json(root / "local-field/external-lock.json", {"schema": 1, "packages": []})

    # bridge: schema 3, pins workspace tools + an absolute dependency path
    bridge_inputs = {
        "lean-toolchain": SHA("d"),
        "IUTBridge.lean": SHA("e"),
        "IUTBridge/Adm.lean": SHA("f"),
        "IUTBridge/Integ.lean": SHA("1"),
        "tools/verify_integrated.py": SHA("2"),
        "@workspace/tools/verify.py": SHA("5"),
        "@workspace/tools/helper.py": SHA("3"),
    }
    bridge_dependencies = {
        (root / "local-field/LocalFieldAudit/Base.lean").as_posix(): SHA("9"),
    }
    bridge_targets = ["IUTBridge.Adm.t1", "IUTBridge.Adm.rect", "IUTBridge.Integ.u1"]
    write_json(root / "bridge/verification/checked-inputs.json", {
        "schema": 3, "input_sha256": bridge_inputs,
        "dependency_sha256": bridge_dependencies, "checked_targets": bridge_targets,
        "receipt_valid": True,
    })
    write_json(root / "bridge/verification/vscode-receipt.json", {
        "schema": 3, "evidence": "verification/obs-bridge.txt", "evidence_sha256": SHA("4"),
        "input_sha256": bridge_inputs, "dependency_sha256": bridge_dependencies,
        "checked_targets": bridge_targets,
    })
    write_text(root / "bridge/verification/obs-bridge.txt", "editor observation\n")
    write_json(root / "bridge/fact-tree/facts.json", bridge_facts())
    write_json(root / "bridge/tools/catalog.json", [
        {"id": "IUTBridge.Adm.t1", "source": "IUTBridge/Adm.lean"},
        {"id": "IUTBridge.Adm.rect", "source": "IUTBridge/Adm.lean"},
        {"id": "IUTBridge.Integ.u1", "source": "IUTBridge/Integ.lean"},
    ])
    write_text(root / "bridge/IUTBridge.lean")
    write_text(root / "bridge/IUTBridge/Adm.lean")
    write_text(root / "bridge/IUTBridge/Integ.lean")
    copy_verifier(root, "bridge", "bridge/tools/verify_integrated.py")
    for name in ("bridge/lean-toolchain", "bridge/lakefile.toml", "bridge/lake-manifest.json"):
        write_text(root / name)

    # cross-project contracts, recorded twice (like contracts.json + facts.json)
    contract = {
        "id": "BR-90",
        "kind": "statement_identity",
        "claim": "fixture contract",
        "abstract": {"project": "main", "theorem": "IUTAudit.Claim.main"},
        "concrete": [{"project": "bridge", "theorem": "IUTBridge.Adm.rect"}],
        "vendored": [
            {"main": "IUTAudit.Core.LeftAllowed", "bridge": "IUTBridge.Adm.LeftAllowed"},
        ],
    }
    write_json(root / "bridges/contracts.json", {"schema": 1, "contracts": [contract]})
    write_json(root / "bridges/facts.json", {
        "schema": 1,
        "projects": {"main": ".", "local": "local-field", "bridge": "bridge"},
        "contracts": [{
            "id": "BR-90", "kind": "statement_identity", "status": "checked",
            "abstract": {"project": "main", "theorem": "IUTAudit.Claim.main"},
            "concrete": ["IUTBridge.Adm.rect"],
        }],
    })
    write_json(root / "bridges/statement-lock.json", {
        "schema": 1,
        "projects": {"main": {"IUTAudit.Core.a": {"statement_sha256": SHA("5")}}},
    })
    write_json(root / "bridges/integrated-lock.json", {
        "schema": 2,
        "entries": {
            "main:IUTAudit.Core.a": {"kind": "theorem", "module": "IUTAudit.Core",
                                     "statement_sha256": SHA("5")},
            "main:IUTAudit.Claim.main": {"kind": "theorem", "module": "IUTAudit.Claim",
                                         "statement_sha256": SHA("6")},
        },
    })


def git(root: Path, *args: str) -> str:
    env = dict(os.environ, **COMMIT_ENV)
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed: {proc.stderr}")
    return proc.stdout


class AffectedTestCase(unittest.TestCase):
    """Base class that materialises a committed fixture repository per test."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name) / "repo"
        self.root.mkdir()
        build_fixture(self.root)
        git(self.root, "init", "-q", "-b", "main")
        git(self.root, "config", "core.autocrlf", "false")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "fixture: recorded evidence")

    # -- helpers -----------------------------------------------------------------
    def run_tool(self, *args: str, expect: int = 0) -> subprocess.CompletedProcess:
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        proc = subprocess.run(
            [sys.executable, str(TOOL), "--repo", str(self.root), *args],
            capture_output=True, text=True, encoding="utf-8", env=env,
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

    @staticmethod
    def node_ids(rows) -> list:
        return [row["id"] for row in rows]


class TestTheorems(AffectedTestCase):
    def test_theorem_source_invalidates_exactly_the_dependent_nodes(self):
        payload = self.payload("--files", "IUTAudit/Core.lean")
        block = payload["theorems"]["per_project"]["main"]
        self.assertEqual(self.node_ids(block["direct"]), ["IUTAudit.Core.a"])
        self.assertEqual(self.node_ids(block["dependents"]), ["IUTAudit.Dep.derived"])
        # the unrelated node in another file is untouched
        self.assertNotIn("IUTAudit.Claim.main", payload["theorems"]["invalidated"])
        self.assertEqual(payload["counts"]["nodes_invalidated"], 2)

    def test_source_change_without_dependents(self):
        payload = self.payload("--files", "IUTAudit/Claim.lean")
        block = payload["theorems"]["per_project"]["main"]
        self.assertEqual(self.node_ids(block["direct"]), ["IUTAudit.Claim.main"])
        self.assertEqual(block["dependents"], [])

    def test_transitive_chain_across_files(self):
        payload = self.payload("--files", "bridge/IUTBridge/Adm.lean")
        block = payload["theorems"]["per_project"]["bridge"]
        self.assertEqual(self.node_ids(block["direct"]), ["IUTBridge.Adm.rect", "IUTBridge.Adm.t1"])
        self.assertEqual(self.node_ids(block["dependents"]), ["IUTBridge.Integ.u1"])
        self.assertEqual(payload["theorems"]["per_project"].keys(), {"bridge"})


class TestReceipts(AffectedTestCase):
    def test_tools_file_voids_the_whole_receipt(self):
        payload = self.payload("--files", "tools/verify.py")
        receipts = self.receipts(payload)
        self.assertTrue(receipts["main"]["void"])
        self.assertEqual(receipts["main"]["nodes_to_pending"], 3)  # every admitted node
        self.assertEqual(payload["counts"]["nodes_to_pending"], 6)  # main + bridge
        # bridge pins the same root file through the @workspace/ prefix
        self.assertTrue(receipts["bridge"]["void"])
        self.assertEqual(
            [(pin["key"], pin["kind"]) for pin in receipts["bridge"]["pins"]],
            [("@workspace/tools/verify.py", "input")],
        )
        self.assertFalse(receipts["local"]["void"])

    def test_workspace_tool_voids_only_the_project_that_pins_it(self):
        payload = self.payload("--files", "tools/helper.py")
        receipts = self.receipts(payload)
        self.assertFalse(receipts["main"]["void"])
        self.assertTrue(receipts["bridge"]["void"])
        self.assertFalse(receipts["local"]["void"])
        self.assertEqual(payload["counts"]["receipts_voided"], 1)

    def test_dependency_pin_voids_the_dependent_project(self):
        payload = self.payload("--files", "local-field/LocalFieldAudit/Base.lean")
        receipts = self.receipts(payload)
        self.assertTrue(receipts["local"]["void"])
        self.assertTrue(receipts["bridge"]["void"])  # dependency_sha256 pin
        self.assertFalse(receipts["main"]["void"])
        kinds = {pin["kind"] for pin in receipts["bridge"]["pins"]}
        self.assertEqual(kinds, {"dependency"})

    def test_evidence_file_is_pinned_by_the_receipt(self):
        payload = self.payload("--files", "bridge/verification/obs-bridge.txt")
        receipts = self.receipts(payload)
        self.assertTrue(receipts["bridge"]["void"])
        self.assertEqual(receipts["bridge"]["pins"][0]["kind"], "evidence")


class TestDocs(AffectedTestCase):
    def test_doc_invalidates_nothing(self):
        for path in ("research/notes.md", "README.md"):
            payload = self.payload("--files", path)
            self.assertEqual(payload["docs"], [path])
            self.assertEqual(payload["counts"]["receipts_voided"], 0)
            self.assertEqual(payload["counts"]["nodes_invalidated"], 0)
            self.assertEqual(payload["counts"]["nodes_to_pending"], 0)
            self.assertEqual(payload["contracts"]["invalidated"], [])
            self.assertFalse(self.receipts(payload)["main"]["void"])
            self.assertFalse(any("re-run" in step or "re-verify" in step for step in payload["redo"]))

    def test_unknown_path_is_reported_but_harmless(self):
        payload = self.payload("--files", "IUTAudit/Gone.lean")
        self.assertEqual(payload["unpinned"], ["IUTAudit/Gone.lean"])
        self.assertEqual(payload["counts"]["receipts_voided"], 0)


class TestContracts(AffectedTestCase):
    def contract_row(self, payload: dict) -> dict:
        rows = {row["id"]: row for row in payload["contracts"]["rows"]}
        return rows["BR-90"]

    def test_concrete_endpoint_source_change_flags_the_contract(self):
        payload = self.payload("--files", "bridge/IUTBridge/Adm.lean")
        row = self.contract_row(payload)
        self.assertTrue(row["invalidated"])
        self.assertEqual(payload["contracts"]["invalidated"], ["BR-90"])
        sources = [r for r in row["reasons"] if r["kind"] == "endpoint-source"]
        self.assertTrue(any(r["role"] == "concrete" and r["path"] == "bridge/IUTBridge/Adm.lean"
                            for r in sources))
        # the vendored definition pair is resolved to both sides
        vendored = [r for r in row["reasons"] if r["kind"] == "endpoint-source" and r["role"] == "vendored"]
        self.assertEqual([r["names"] for r in vendored], [["IUTBridge.Adm.LeftAllowed"]])

    def test_vendored_definition_change_on_the_abstract_side(self):
        payload = self.payload("--files", "IUTAudit/Core.lean")
        row = self.contract_row(payload)
        self.assertTrue(row["invalidated"])
        vendored = [r for r in row["reasons"] if r["kind"] == "endpoint-source" and r["role"] == "vendored"]
        self.assertEqual([r["names"] for r in vendored], [["IUTAudit.Core.LeftAllowed"]])

    def test_transitive_endpoint_flags_the_contract(self):
        # IUTBridge.Integ.u1 is not an endpoint; rect (now invalidated) is.
        payload = self.payload("--files", "bridge/IUTBridge/Adm.lean")
        row = self.contract_row(payload)
        self.assertTrue(row["invalidated"])
        self.assertIn("bridge", row["admission_lost"])

    def test_contract_record_change_flags_every_contract(self):
        payload = self.payload("--files", "bridges/contracts.json")
        row = self.contract_row(payload)
        kinds = {reason["kind"] for reason in row["reasons"]}
        self.assertIn("contract-record", kinds)
        self.assertEqual(payload["changed"][0]["classes"], ["contract-record"])


class TestModes(AffectedTestCase):
    def test_range_matches_explicit_files(self):
        core = self.root / "IUTAudit/Core.lean"
        core.write_text("changed\n", encoding="utf-8")
        git(self.root, "commit", "-q", "-am", "touch Core.lean")
        by_range = self.payload("--range", "HEAD~1..HEAD")
        by_files = self.payload("--files", "IUTAudit/Core.lean")
        self.assertEqual(by_range["mode"]["kind"], "range")
        self.assertEqual(by_range["mode"]["commit_count"], 1)
        self.assertEqual(by_range["mode"]["commits"][0]["subject"], "touch Core.lean")
        self.assertEqual(by_range["theorems"]["invalidated"], by_files["theorems"]["invalidated"])
        self.assertEqual(by_range["receipts"], by_files["receipts"])

    def test_empty_range_is_clean(self):
        payload = self.payload("--range", "HEAD..HEAD")
        self.assertEqual(payload["changed"], [])
        self.assertEqual(payload["counts"]["nodes_invalidated"], 0)
        self.assertEqual(payload["redo"], [])

    def test_staged_mode(self):
        notes = self.root / "research/notes.md"
        notes.write_text("# notes, edited\n", encoding="utf-8")
        git(self.root, "add", "research/notes.md")
        payload = self.payload("--staged")
        self.assertEqual(payload["mode"]["kind"], "staged")
        self.assertEqual([row["path"] for row in payload["changed"]], ["research/notes.md"])
        self.assertEqual(payload["docs"], ["research/notes.md"])
        self.assertEqual(payload["counts"]["receipts_voided"], 0)

    def test_rename_is_reported_on_both_sides(self):
        git(self.root, "mv", "IUTAudit/Dep.lean", "IUTAudit/DepRenamed.lean")
        git(self.root, "commit", "-q", "-m", "rename Dep.lean")
        payload = self.payload("--range", "HEAD~1..HEAD")
        paths = [row["path"] for row in payload["changed"]]
        self.assertIn("IUTAudit/Dep.lean", paths)
        self.assertIn("IUTAudit/DepRenamed.lean", paths)

    def test_json_is_deterministic(self):
        first = self.run_tool("--files", "bridge/IUTBridge/Adm.lean", "--json").stdout
        second = self.run_tool("--files", "bridge/IUTBridge/Adm.lean", "--json").stdout
        self.assertEqual(first, second)

    def test_human_output_has_the_hand_reconstruction_section(self):
        text = self.run_tool("--files", "bridge/IUTBridge/Adm.lean").stdout
        self.assertIn("WHAT ASTRA WOULD OTHERWISE HAVE TO RECONSTRUCT BY HAND", text)
        self.assertIn("WHAT MUST BE REDONE", text)
        self.assertIn("RECEIPTS", text)


class TestErrors(AffectedTestCase):
    def test_unknown_revision_is_a_clear_error(self):
        proc = self.run_tool("--range", "deadbeef..HEAD", expect=1)
        self.assertIn("affected.py: error:", proc.stderr)
        self.assertIn("unknown revision", proc.stderr)

    def test_missing_records_is_a_clear_error(self):
        empty = Path(self._tmp.name) / "empty"
        empty.mkdir()
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        proc = subprocess.run(
            [sys.executable, str(TOOL), "--repo", str(empty), "--files", "x.lean"],
            capture_output=True, text=True, encoding="utf-8", env=env,
        )
        self.assertEqual(proc.returncode, 1)
        self.assertIn("no verification records", proc.stderr)

    def test_missing_mode_is_a_usage_error(self):
        proc = self.run_tool(expect=2)
        self.assertIn("--range, --files or --staged is required", proc.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
