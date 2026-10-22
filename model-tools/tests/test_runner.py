from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


RUNNER_PATH = Path(__file__).resolve().parents[1] / "run.py"
spec = importlib.util.spec_from_file_location("model_runner", RUNNER_PATH)
runner = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = runner
spec.loader.exec_module(runner)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class RunnerProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=RUNNER_PATH.parent)
        self.out = Path(self.temp.name) / "out"
        self.out.mkdir()
        self.worktree = Path(self.temp.name) / "project"
        self.project = self.worktree / "Candidates" / "orbit-quotient"
        self.project.mkdir(parents=True)
        self.request = {"schema": 1, "p": 5, "N": 3, "thresholds": [1], "permutations": [[0]],
                        "require_enlargement": False}
        self.claims = {"hull_thresholds": [1], "witnesses": [{"permutation_index": 0, "source_coordinate": 0}],
                       "box_exponent": 2, "hull_exponent": 2, "cardinality": {"base": 5}}
        self.cert = b"import Candidates.HullTool\nnamespace HullToolCertificate\nend HullToolCertificate\n"
        self.test_spec = {"worktree": self.worktree, "component": "orbit-quotient", "manifest_component": "hull", "helper_target": "Candidates.HullTool",
                          "theorem_prefix": "HullToolCertificate.",
                          "theorems": {"input_valid", "action_convention", "witnesses_valid", "exponents_valid",
                                       "thresholds_eq_hull", "product_minimality", "cardinality", "identity_mem", "enlargement"},
                          "optional_theorems": {"identity_mem", "enlargement"},
                          "claims": {"hull_thresholds", "witnesses", "box_exponent", "hull_exponent", "cardinality"},
                          "result_container": "flat"}
        self._write_fixture()

    def tearDown(self):
        self.temp.cleanup()

    def _write_fixture(self):
        request_bytes = (json.dumps(self.request, ensure_ascii=False, indent=2) + "\n").encode()
        (self.out / "request.json").write_bytes(request_bytes)
        (self.out / "result.json").write_text(json.dumps({"status": "PROPOSED", **self.claims}), encoding="utf-8")
        (self.out / "certificate.lean").write_bytes(self.cert)
        request_hash = digest(request_bytes)
        manifest = {"schema": 1, "component": "hull", "project": str(self.worktree), "status": "PROPOSED",
                    "prepare_target": "Candidates.HullTool", "certificate": str(self.out / "certificate.lean"),
                    "certificate_sha256": digest(self.cert), "request_sha256": request_hash,
                    "theorem_names": ["HullToolCertificate." + name for name in
                                      ("input_valid", "action_convention", "witnesses_valid", "exponents_valid",
                                       "thresholds_eq_hull", "product_minimality", "cardinality")],
                    "result": self.claims}
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")

    def test_valid_proposal_passes_protocol_gate(self):
        manifest, result, cert, names = runner.validate_manifest("hull", self.test_spec, self.out, self.request)
        self.assertEqual(manifest["status"], "PROPOSED")
        self.assertEqual(result["status"], "PROPOSED")
        self.assertEqual(cert, self.cert)
        self.assertEqual(len(names), 7)

    def test_supplied_nested_input_may_gain_a_documented_default(self):
        self.assertTrue(runner.preserves_supplied({"domain": {"kind": "finite_profiles", "base_index": 0}},
                                                  {"domain": {"kind": "finite_profiles"}}))
        self.assertFalse(runner.preserves_supplied({"x": 1}, {"x": True}))

    def test_missing_certificate_is_rejected(self):
        (self.out / "certificate.lean").unlink()
        with self.assertRaisesRegex(runner.ToolError, "omitted required output"):
            runner.validate_manifest("hull", self.test_spec, self.out, self.request)

    def test_corrupt_certificate_hash_is_rejected(self):
        (self.out / "certificate.lean").write_bytes(self.cert + b"-- changed\n")
        with self.assertRaisesRegex(runner.ToolError, "certificate_sha256"):
            runner.validate_manifest("hull", self.test_spec, self.out, self.request)

    def test_request_hash_is_required(self):
        manifest = json.loads((self.out / "manifest.json").read_text(encoding="utf-8"))
        manifest.pop("request_sha256")
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        with self.assertRaisesRegex(runner.ToolError, "request_sha256"):
            runner.validate_manifest("hull", self.test_spec, self.out, self.request)

    def test_insufficient_domain_is_returned_without_lean_claims(self):
        result = {"schema": 1, "status": "INSUFFICIENT", "reason": "missing finite profile domain"}
        (self.out / "result.json").write_text(json.dumps(result), encoding="utf-8")
        manifest = json.loads((self.out / "manifest.json").read_text(encoding="utf-8"))
        manifest.update(status="INSUFFICIENT", theorem_names=[], result=result)
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        checked, emitted, cert, names = runner.validate_manifest("hull", self.test_spec, self.out, self.request)
        self.assertEqual(checked["status"], "INSUFFICIENT")
        self.assertEqual(emitted["status"], "INSUFFICIENT")
        self.assertEqual(names, [])

    def test_axiom_allowlist_is_enforced(self):
        stdout = self.out / "lean.stdout.log"
        stderr = self.out / "lean.stderr.log"
        theorem = "HullToolCertificate.cardinality"
        stdout.write_text(f"info: '{theorem}' depends on axioms: [propext, Quot.sound]\n", encoding="utf-8")
        stderr.write_text("", encoding="utf-8")
        ok, _ = runner.check_axioms(stdout, [theorem])
        self.assertTrue(ok)
        stdout.write_text(f"info: '{theorem}' depends on axioms: [sorryAx]\n", encoding="utf-8")
        ok, _ = runner.check_axioms(stdout, [theorem])
        self.assertFalse(ok)

    def test_fixed_emitter_recomputation_binds_claims_to_certificate(self):
        component = Path(self.temp.name) / "fixed_emitter.py"
        component.write_text(
            "def validate(data): return data\n"
            "def compute(data): return {'value': data['value']}\n"
            "def certificate(data, result): return ('theorem claim : ' + str(result['value']), ['Fixed.claim'])\n",
            encoding="utf-8",
        )
        req = {"value": 7}
        cert = b"theorem claim : 7"
        runner.verify_emitter_binding("hull", component, req, req, {"value": 7}, cert, ["Fixed.claim"])
        with self.assertRaisesRegex(runner.ToolError, "exact certificate"):
            runner.verify_emitter_binding("hull", component, req, req, {"value": 7}, b"theorem claim : True", ["Fixed.claim"])

    def test_ledger_proposal_requires_fixed_seven_theorems_and_nested_result(self):
        request = {"schema": 1, "p": 5, "weights": [1], "permutation": [0],
                   "scalar_valuations": [0], "domain": {"kind": "finite_profiles", "profiles": [[0]], "base_index": 0}}
        claims = {"ledger_preserved": True, "domain_invariant": True, "d": [0], "scalar_budget": 0,
                  "base_equation": 0, "profile_shifts": [0], "image_profiles": [[0]], "generators": [],
                  "generator_count": 0, "generator_values": [], "hgen_coefficients": [[]],
                  "generator_method": "integer_column_euclid", "generator_claim": "two inclusions",
                  "witness": None, "domain_witness": None, "scope": "finite explicit profiles"}
        cert = b"-- fixed ledger certificate fixture\n"
        request_bytes = (json.dumps(request, ensure_ascii=False, indent=2) + "\n").encode()
        (self.out / "request.json").write_bytes(request_bytes)
        (self.out / "result.json").write_text(json.dumps({"schema": 1, "status": "PROPOSED", "result": claims}), encoding="utf-8")
        (self.out / "certificate.lean").write_bytes(cert)
        theorem_suffixes = ["span_generation", "span_membership", "domain_nonempty", "scalars_nonzero",
                            "numeric_result", "ledger_result", "domain_result"]
        manifest = {"schema": 1, "component": "restricted-ledger", "project": str(self.worktree),
                    "status": "PROPOSED", "prepare_target": "Candidates.LedgerTool",
                    "certificate": str(self.out / "certificate.lean"), "certificate_sha256": digest(cert),
                    "request_sha256": digest(request_bytes), "theorem_names": ["GeneratedLedger." + n for n in theorem_suffixes],
                    "result": claims}
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        # Exercise the production allowlist, so a missing registered optional theorem
        # cannot be concealed by an independently reconstructed test specification.
        ledger_spec = dict(runner.SPECS['ledger'], worktree=self.worktree)
        _, emitted, _, names = runner.validate_manifest("ledger", ledger_spec, self.out, request)
        self.assertEqual(emitted["result"], claims)
        self.assertEqual(len(names), 7)

        # A failed ledger claim must carry the theorem binding the actual witness values.
        claims.update(ledger_preserved=False, witness={"ledger_before": 0, "ledger_after": 1, "shift": 1})
        (self.out / "result.json").write_text(json.dumps({"schema": 1, "status": "PROPOSED", "result": claims}), encoding="utf-8")
        manifest = json.loads((self.out / "manifest.json").read_text(encoding="utf-8"))
        manifest["result"] = claims
        manifest["theorem_names"].append("GeneratedLedger.witness_values")
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        _, _, _, names = runner.validate_manifest("ledger", ledger_spec, self.out, request)
        self.assertIn("GeneratedLedger.witness_values", names)

        manifest["theorem_names"].remove("GeneratedLedger.witness_values")
        (self.out / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        with self.assertRaisesRegex(runner.ToolError, "witness_values theorem presence"):
            runner.validate_manifest("ledger", ledger_spec, self.out, request)

    def test_component_timeout_is_bounded_and_logged(self):
        stdout, stderr = self.out / "stdout.log", self.out / "stderr.log"
        code, elapsed = runner.run_bounded([sys.executable, "-c", "import time; time.sleep(5)"],
                                           self.worktree, stdout, stderr, 0.2)
        self.assertEqual(code, 124)
        self.assertLess(elapsed, 5)
        self.assertTrue(stdout.exists())
        self.assertTrue(stderr.exists())


if __name__ == "__main__":
    unittest.main()
