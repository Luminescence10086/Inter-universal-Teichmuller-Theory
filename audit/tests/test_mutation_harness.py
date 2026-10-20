"""Tests for audit/mutation_harness.py.

The harness is the unit under test, so the checks are about its *verdicts*: each
mutation that a gate claims to catch must actually be caught, the innocuous
negative control must not be read as statement drift, and the gates must pass
unmutated copies (otherwise "anything changed = fail" would masquerade as
strength).

Runtime: the module-scoped fixture runs the harness once (~18 s: it copies a
project tree per mutation, re-runs the real ledgers and one full
``freshness.validate_project``) and the JSON test runs it twice more, so the
suite takes about a minute.  Nothing outside ``audit/`` and the harness's own
temporary directories is written.

  python -m unittest discover -s audit/tests -v
"""
from __future__ import annotations

import contextlib
import io
import json
import sys
import unittest
from pathlib import Path

AUDIT = Path(__file__).resolve().parents[1]
if str(AUDIT) not in sys.path:
    sys.path.insert(0, str(AUDIT))

import mutation_harness as mh  # noqa: E402

RESULT = None

# The claim each gate makes, and therefore the cell that must read CAUGHT.
EXPECTED = {
    "M1": ("statement_lock", "semantic_lock"),
    "M2": ("statement_lock", "semantic_lock"),
    "M3": ("hypothesis_gate", "input_hash"),
    "M4": ("axiom_gate", "statement_lock", "semantic_lock"),
    "M5": ("contract_body", "semantic_lock"),
    "M6": ("statement_lock", "semantic_lock"),
    "M7": ("input_hash",),
    # the negative control still has one expected catch: the source bytes changed,
    # so the byte/input gate must refuse -- the point is that the *statement* gates
    # stay silent.
    "M8": ("input_hash",),
}
# The negative control must not reach the gates it is not about.
CONTROL_MUST_BE_SILENT = ("statement_lock", "semantic_lock")


def setUpModule():
    global RESULT
    RESULT = mh.run()


def _row(result, mutation_id):
    return next(row for row in result["matrix"] if row["id"] == mutation_id)


class MatrixShape(unittest.TestCase):
    def test_one_row_per_mutation_and_one_cell_per_gate(self):
        ids = [row["id"] for row in RESULT["matrix"]]
        self.assertEqual(ids, ["M1", "M2", "M3", "M4", "M5", "M6", "M7", "M8"])
        for row in RESULT["matrix"]:
            self.assertEqual(tuple(row["cells"]), mh.GATES, row["id"])

    def test_every_cell_uses_one_of_the_three_labels(self):
        allowed = {mh.CAUGHT, mh.MISSED, mh.NA}
        for row in RESULT["matrix"]:
            for gate, cell in row["cells"].items():
                self.assertIn(cell["verdict"], allowed, f"{row['id']}/{gate}")
                self.assertTrue(cell["detail"], f"{row['id']}/{gate} has no detail")

    def test_not_applicable_cells_say_why(self):
        for row in RESULT["matrix"]:
            for gate, cell in row["cells"].items():
                if cell["verdict"] == mh.NA:
                    self.assertIn("reason", cell, f"{row['id']}/{gate}")
                    self.assertGreater(len(cell["reason"]), 20)

    def test_mutations_are_observable(self):
        for row in RESULT["matrix"]:
            self.assertTrue(row["caught_by"], f"{row['id']} was caught by no gate")

    def test_expectations_name_real_gates(self):
        for mutation_id, gates in EXPECTED.items():
            for gate in gates:
                self.assertIn(gate, mh.GATES, mutation_id)


class RequiredMutationsAreCaught(unittest.TestCase):
    def test_m1_to_m7_are_caught_by_the_gate_that_claims_them(self):
        for mutation_id, gates in EXPECTED.items():
            row = _row(RESULT, mutation_id)
            for gate in gates:
                with self.subTest(mutation=mutation_id, gate=gate):
                    self.assertEqual(row["cells"][gate]["verdict"], mh.CAUGHT,
                                     row["cells"][gate]["detail"])

    def test_declared_expectations_match_the_matrix(self):
        for row in RESULT["matrix"]:
            self.assertEqual(tuple(row["expect"]), EXPECTED.get(row["id"], ()),
                             row["id"])

    def test_statement_weakening_and_alteration_are_ledgered(self):
        for mutation_id in ("M1", "M2"):
            detail = _row(RESULT, mutation_id)["cells"]["statement_lock"]["detail"]
            self.assertIn("FAIL changed", detail)
            self.assertIn("(statement)", detail)

    def test_axiom_regression_is_caught_by_the_whitelist_too(self):
        detail = _row(RESULT, "M4")["cells"]["axiom_gate"]["detail"]
        self.assertIn(mh.BAD_AXIOM, detail)
        self.assertIn("unapproved", detail)

    def test_hypothesis_drift_names_the_disagreement(self):
        detail = _row(RESULT, "M3")["cells"]["hypothesis_gate"]["detail"]
        self.assertIn("Undeclared or stale hypotheses", detail)
        self.assertIn(mh.ANCHOR_CATALOG, detail)

    def test_vendored_body_flip_keeps_the_elaborated_type(self):
        detail = _row(RESULT, "M5")["cells"]["contract_body"]["detail"]
        self.assertIn("body mismatch", detail)
        self.assertNotIn("type mismatch", detail)

    def test_node_removal_fails_the_ledgers(self):
        for gate in ("statement_lock", "semantic_lock"):
            detail = _row(RESULT, "M6")["cells"][gate]["detail"]
            self.assertIn(mh.ANCHOR_STATEMENT, detail)

    def test_byte_drift_names_the_changed_file(self):
        detail = _row(RESULT, "M7")["cells"]["input_hash"]["detail"]
        self.assertIn(mh.ANCHOR_BYTE_FILE, detail)


class NegativeControl(unittest.TestCase):
    def test_statement_gates_are_silent_on_an_innocuous_edit(self):
        row = _row(RESULT, "M8")
        for gate in CONTROL_MUST_BE_SILENT:
            with self.subTest(gate=gate):
                self.assertEqual(row["cells"][gate]["verdict"], mh.MISSED,
                                 "the statement gate read an innocuous edit as drift")

    def test_the_byte_gate_does_fire_and_the_report_says_so(self):
        row = _row(RESULT, "M8")
        self.assertEqual(row["cells"]["input_hash"]["verdict"], mh.CAUGHT)
        self.assertIn(mh.ANCHOR_COMMENT_FILE,
                      row["cells"]["input_hash"]["detail"])

    def test_statement_gates_are_not_byte_sensitive_for_either_direction(self):
        # M1/M2 refresh the export the way a verifier re-run would, so the byte
        # gate passes while the ledger fails: per-gate reporting, not globality.
        for mutation_id in ("M1", "M2"):
            row = _row(RESULT, mutation_id)
            self.assertEqual(row["cells"]["input_hash"]["verdict"], mh.MISSED)
            self.assertEqual(row["cells"]["statement_lock"]["verdict"], mh.CAUGHT)


class Probes(unittest.TestCase):
    def test_unmutated_copies_pass_every_applicable_gate(self):
        for name in ("baseline_bridge", "baseline_main"):
            probe = RESULT["probes"][name]
            self.assertTrue(probe["ok"], f"{name}: {probe['detail']}")

    def test_fact_tree_and_clean_checkout_probes(self):
        self.assertTrue(RESULT["probes"]["fact_tree_removal"]["ok"])
        self.assertEqual(
            RESULT["probes"]["fact_tree_removal"]["detail"],
            "<copy>: not fully admitted, or stale target set")
        self.assertTrue(RESULT["probes"]["clean_checkout_head"]["ok"])

    def test_unpinning_a_ledger_entry_passes_by_design(self):
        self.assertTrue(RESULT["probes"]["unpin_entry"]["ok"])
        self.assertIn("addition", RESULT["probes"]["unpin_entry"]["detail"])

    def test_the_repository_was_not_touched(self):
        self.assertTrue(RESULT["repository_unchanged"])

    def test_exit_code_is_zero_when_every_claim_holds(self):
        self.assertEqual(RESULT["violations"], [])
        self.assertEqual(RESULT["exit_code"], 0)


class ExitCodeContract(unittest.TestCase):
    """The "non-zero if a claim is broken" rule, tested without a harness run."""

    @staticmethod
    def _cells(verdicts):
        return {gate: {"verdict": verdict, "detail": "synthetic"}
                for gate, verdict in verdicts.items()}

    def test_a_missed_claim_is_a_violation(self):
        spec = {"id": "MX", "expect": ("statement_lock",), "must_not": ()}
        cells = self._cells({"statement_lock": mh.MISSED})
        self.assertEqual(mh.violations_for(spec, cells),
                         ["MX: statement_lock was expected to catch this mutation "
                          "and did not"])

    def test_a_flagged_negative_control_is_a_violation(self):
        spec = {"id": "MX", "expect": (), "must_not": ("statement_lock",)}
        cells = self._cells({"statement_lock": mh.CAUGHT})
        self.assertEqual(len(mh.violations_for(spec, cells)), 1)

    def test_a_silent_negative_control_is_not_a_violation(self):
        spec = {"id": "MX", "expect": ("input_hash",),
                "must_not": ("statement_lock",)}
        cells = self._cells({"input_hash": mh.CAUGHT,
                             "statement_lock": mh.MISSED})
        self.assertEqual(mh.violations_for(spec, cells), [])


class CommandLine(unittest.TestCase):
    def _run_cli(self, argv):
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = mh.main(argv)
        return code, buffer.getvalue()

    def test_json_mode_is_parseable_deterministic_and_timestamp_free(self):
        first_code, first = self._run_cli(["--json"])
        second_code, second = self._run_cli(["--json"])
        self.assertEqual((first_code, second_code), (0, 0))
        self.assertEqual(first, second, "the report is not deterministic")
        report = json.loads(first)
        self.assertEqual(report["exit_code"], 0)
        self.assertEqual(len(report["matrix"]), len(mh.MUTATIONS))
        self.assertNotIn("generated_utc", first)

    def test_json_matches_a_direct_run(self):
        _, text = self._run_cli(["--json"])
        report = json.loads(text)
        self.assertEqual(report["matrix"], json.loads(json.dumps(RESULT["matrix"])))


if __name__ == "__main__":
    unittest.main()
