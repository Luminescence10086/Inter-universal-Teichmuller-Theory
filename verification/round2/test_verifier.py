"""Regression tests for fact-tree admission policy, without modifying project facts.

Run with ``python tools/test_verifier.py`` or ``python -m unittest tools.test_verifier``.
The constant graphs below model exported Lean terms; no editor receipts are fabricated
and no production verifier run or external code execution is needed by these tests.
"""
from __future__ import annotations

import subprocess
import sys
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify  # noqa: E402


def constant(name: str, *dependencies: str, kind: str = "definition",
             module: str = "IUTAudit.Descent") -> dict:
    return {"id": name, "constants": list(dependencies), "kind": kind, "module": module}


class HelperDependencyTests(unittest.TestCase):
    def test_plift_helper_exposes_unadmitted_base_theorem(self):
        """Actual regression: visible := hiddenHelper.down, helper := PLift.mk base."""
        base = "IUTAudit.Scale.hidden_base"
        helper = "IUTAudit.Descent.hiddenHelper"
        visible = "IUTAudit.Descent.visible"
        rows = [constant(base, "True.intro", kind="theorem", module="IUTAudit.Scale"),
                constant(helper, "PLift.mk", base),
                constant(visible, "PLift.down", helper, kind="theorem")]
        by_id = {row["id"]: row for row in rows}
        deps = verify.dependencies_via_helpers(visible, by_id, {base, visible})
        self.assertEqual(deps, {base})
        self.assertEqual(verify.admission_closure({visible}, {visible: deps, base: set()}), set())

    def test_multilevel_generated_helpers_and_shared_paths(self):
        rows = [constant("B", "B._proof_1_1", "shared", kind="theorem"),
                constant("B._proof_1_1", "nested", "shared", kind="theorem"),
                constant("nested", "A"), constant("shared", "nested", "C"),
                constant("A", kind="theorem"), constant("C", kind="theorem")]
        by_id = {row["id"]: row for row in rows}
        self.assertEqual(verify.dependencies_via_helpers("B", by_id, {"A", "B", "C"}),
                         {"A", "C"})

    def test_helper_cycle_terminates_and_preserves_reachable_targets(self):
        rows = [constant("B", "h1", kind="theorem"), constant("h1", "h2"),
                constant("h2", "h1", "A"), constant("A", kind="theorem")]
        by_id = {row["id"]: row for row in rows}
        self.assertEqual(verify.dependencies_via_helpers("B", by_id, {"A", "B"}), {"A"})

    def test_stop_at_target_instead_of_adding_transitive_shortcut(self):
        rows = [constant("B", "helper", kind="theorem"), constant("helper", "A"),
                constant("A", "C", kind="theorem"), constant("C", kind="theorem")]
        by_id = {row["id"]: row for row in rows}
        self.assertEqual(verify.dependencies_via_helpers("B", by_id, {"A", "B", "C"}), {"A"})
        self.assertEqual(verify.dependencies_via_helpers("A", by_id, {"A", "B", "C"}), {"C"})

    def test_terminal_library_constants_are_not_invented_as_targets(self):
        by_id = {"B": constant("B", "True.intro", "Eq.refl", kind="theorem")}
        self.assertEqual(verify.dependencies_via_helpers("B", by_id, {"B"}), set())


class AdmissionClosureTests(unittest.TestCase):
    def test_remove_chain_to_missing_eligible_dependency_until_fixed_point(self):
        eligible = {"B", "C", "D", "independent"}
        deps = {"A": set(), "B": {"A"}, "C": {"B"}, "D": {"C"}, "independent": set()}
        self.assertEqual(verify.admission_closure(eligible, deps), {"independent"})
        self.assertEqual(eligible, {"B", "C", "D", "independent"})

    def test_complete_chain_is_preserved(self):
        deps = {"A": set(), "B": {"A"}, "C": {"A", "B"}}
        self.assertEqual(verify.admission_closure(set(deps), deps), set(deps))

    def test_one_missing_diamond_branch_invalidates_join(self):
        deps = {"base": set(), "left": {"base"}, "right": {"missing"},
                "join": {"left", "right"}}
        self.assertEqual(verify.admission_closure(set(deps), deps), {"base", "left"})

    def test_empty_eligibility_admits_nothing(self):
        self.assertEqual(verify.admission_closure(set(), {"A": set()}), set())


class ProcessDiagnosticTests(unittest.TestCase):
    def test_successful_empty_stderr_is_accepted(self):
        result = subprocess.CompletedProcess(["lean"], 0, stdout="information", stderr="")
        verify.check_process(result, "export")

    def test_zero_exit_with_stderr_warning_is_rejected(self):
        result = subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="warning: probe\n")
        with self.assertRaises(RuntimeError):
            verify.check_process(result, "source")

    def test_even_whitespace_stderr_is_not_silently_ignored(self):
        result = subprocess.CompletedProcess(["lean"], 0, stdout="", stderr=" \n")
        with self.assertRaises(RuntimeError):
            verify.check_process(result, "source")

    def test_nonzero_exit_without_stderr_is_rejected(self):
        result = subprocess.CompletedProcess(["lean"], 1, stdout="failed", stderr="")
        with self.assertRaises(RuntimeError):
            verify.check_process(result, "source")


class SnapshotTests(unittest.TestCase):
    def test_identical_snapshot_with_different_dict_order_is_accepted(self):
        verify.assert_snapshot({"A.lean": "a", "B.lean": "b"},
                               {"B.lean": "b", "A.lean": "a"})

    def test_source_hash_change_is_rejected(self):
        with self.assertRaises(RuntimeError):
            verify.assert_snapshot({"A.lean": "before"}, {"A.lean": "after"})

    def test_new_file_is_rejected_even_when_existing_hashes_match(self):
        with self.assertRaises(RuntimeError):
            verify.assert_snapshot({"A.lean": "a"}, {"A.lean": "a", "New.lean": "n"})

    def test_removed_file_is_rejected(self):
        with self.assertRaises(RuntimeError):
            verify.assert_snapshot({"A.lean": "a", "Removed.lean": "r"}, {"A.lean": "a"})


class CatalogValidationTests(unittest.TestCase):
    def setUp(self):
        self.catalog = [{"id": "IUTAudit.Descent.example", "source": "IUTAudit/Descent.lean"}]
        self.by_id = {"IUTAudit.Descent.example": constant("IUTAudit.Descent.example",
                                                         kind="theorem")}

    def test_valid_explicit_target_is_accepted(self):
        verify.validate_catalog(self.catalog, self.by_id)

    def test_duplicate_id_is_rejected(self):
        with self.assertRaises(RuntimeError):
            verify.validate_catalog(self.catalog + [dict(self.catalog[0])], self.by_id)

    def test_missing_elaborated_target_is_rejected(self):
        with self.assertRaises(RuntimeError):
            verify.validate_catalog(self.catalog, {})

    def test_definition_cannot_masquerade_as_catalog_theorem(self):
        self.by_id["IUTAudit.Descent.example"]["kind"] = "definition"
        with self.assertRaises(RuntimeError):
            verify.validate_catalog(self.catalog, self.by_id)

    def test_module_must_match_source_not_theorem_namespace(self):
        self.by_id["IUTAudit.Descent.example"]["module"] = "IUTAudit.Scale"
        with self.assertRaises(RuntimeError):
            verify.validate_catalog(self.catalog, self.by_id)

    def test_theorem_namespace_may_differ_from_its_source_module(self):
        catalog = [{"id": "OtherNamespace.example", "source": "IUTAudit/Descent.lean"}]
        by_id = {"OtherNamespace.example": constant("OtherNamespace.example", kind="theorem")}
        verify.validate_catalog(catalog, by_id)

    def test_nested_source_path_converts_to_full_dotted_module(self):
        catalog = [{"id": "Arbitrary.example", "source": "IUTAudit/Nested/Extra.lean"}]
        by_id = {"Arbitrary.example": constant("Arbitrary.example", kind="theorem",
                                               module="IUTAudit.Nested.Extra")}
        verify.validate_catalog(catalog, by_id)


class EditorReceiptBindingTests(unittest.TestCase):
    """Exercise receipt binding in an isolated root; never touch real UI evidence."""

    def setUp(self):
        temporary_parent = Path(__file__).resolve().parents[1] / ".tmp-round2-verifier"
        temporary_parent.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix="iut-receipt-test-",
                                                     dir=temporary_parent)
        if not Path(self.temporary.name).resolve().is_relative_to(temporary_parent.resolve()):
            raise RuntimeError("Unexpected receipt test directory outside workspace")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.observation = self.root / "verification/vscode-observation-round2.txt"
        self.observation.parent.mkdir()
        self.observation.write_text("SYNTHETIC UNIT TEST, not a VS Code observation.\n",
                                    encoding="utf-8")
        self.root_patch = patch.object(verify, "ROOT", self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.inputs = {"IUTAudit/Descent.lean": "source-version-a"}
        self.runtime = {"toolchain/lean.exe": "runtime-version-a"}
        self.catalog = [{"id": "Project.B", "source": "IUTAudit/Descent.lean"},
                        {"id": "Project.A", "source": "IUTAudit/Descent.lean"}]
        self.receipt = {
            "schema": 2,
            "input_sha256": copy.deepcopy(self.inputs),
            "runtime_sha256": copy.deepcopy(self.runtime),
            "evidence_sha256": hashlib.sha256(self.observation.read_bytes()).hexdigest(),
            "checked_targets": ["Project.A", "Project.B"],
            "information_messages": 4,
        }

    def valid(self):
        return verify.receipt_valid(self.receipt, self.inputs, self.runtime, self.catalog)

    def test_matching_receipt_and_evidence_are_accepted(self):
        self.assertTrue(self.valid())

    def test_missing_observation_file_is_rejected(self):
        self.observation.unlink()
        self.assertFalse(self.valid())

    def test_wrong_observation_hash_is_rejected(self):
        self.receipt["evidence_sha256"] = "0" * 64
        self.assertFalse(self.valid())

    def test_changed_observation_bytes_are_rejected(self):
        self.observation.write_text("different synthetic observation\n", encoding="utf-8")
        self.assertFalse(self.valid())

    def test_missing_checked_target_is_rejected(self):
        self.receipt["checked_targets"] = ["Project.A"]
        self.assertFalse(self.valid())

    def test_changed_source_context_is_rejected(self):
        self.inputs["IUTAudit/Descent.lean"] = "source-version-b"
        self.assertFalse(self.valid())

    def test_changed_runtime_context_is_rejected(self):
        self.runtime["toolchain/lean.exe"] = "runtime-version-b"
        self.assertFalse(self.valid())

    def test_wrong_information_message_count_is_rejected(self):
        self.receipt["information_messages"] = 2
        self.assertFalse(self.valid())

    def test_old_receipt_schema_is_rejected(self):
        self.receipt["schema"] = 1
        self.assertFalse(self.valid())


if __name__ == "__main__":
    unittest.main(verbosity=2)
