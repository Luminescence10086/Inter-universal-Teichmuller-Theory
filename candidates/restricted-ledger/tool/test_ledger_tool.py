"""Deterministic standard-library checks; Lean replay is a separate required step."""
import copy
import json
from pathlib import Path
import random
import tempfile
import unittest
import ledger_tool as tool


BASE = {"schema": 1, "p": 2, "weights": [1, 2], "permutation": [1, 0],
        "scalar_valuations": [0, 0], "domain": {"kind": "finite_profiles",
        "profiles": [[0, 0], [1, 1], [-1, -1]], "base_index": 0}}


class LedgerToolTests(unittest.TestCase):
    def test_integer_span_and_inverse_randomized(self):
        rng = random.Random(442)
        for n in range(1, 6):
            for m in range(1, 9):
                for _ in range(10):
                    e = [[rng.randint(-30, 30) for _ in range(n)] for _ in range(m)]
                    base = rng.randrange(m)
                    b, g, h, v, inv = tool.integer_generators(e, base)
                    self.assertLessEqual(len(b), n)
                    for k in range(m):
                        for j in range(n):
                            self.assertEqual(e[k][j] - e[base][j], sum(g[k][i]*b[i][j] for i in range(len(b))))
                    for i in range(len(b)):
                        for j in range(n):
                            self.assertEqual(b[i][j], sum(h[i][k]*(e[k][j]-e[base][j]) for k in range(m)))
                    for i in range(m):
                        for j in range(m):
                            self.assertEqual(sum(v[i][k]*inv[k][j] for k in range(m)), int(i == j))

    def test_nonrealized_generator(self):
        b, g, h, _, _ = tool.integer_generators([[0], [2], [3]], 0)
        self.assertEqual(b, [[1]])
        self.assertEqual(g, [[0], [2], [3]])
        self.assertEqual(h, [[0, -1, 1]])

    def test_restricted_preservation(self):
        result = tool.calculate(tool.validate(BASE))
        self.assertTrue(result["ledger_preserved"])
        self.assertTrue(result["domain_invariant"])
        self.assertNotEqual(result["d"], [0, 0])

    def test_scalar_budget_and_concrete_witness(self):
        req = copy.deepcopy(BASE)
        req["scalar_valuations"] = [1, 0]
        result = tool.calculate(tool.validate(req))
        self.assertFalse(result["ledger_preserved"])
        self.assertEqual(result["scalar_budget"], 2)
        self.assertEqual(result["witness"]["ledger_shift"], 2)

    def test_separate_domain_obligation_rank_zero(self):
        req = copy.deepcopy(BASE)
        req.update(weights=[0, 0], permutation=[0, 1], scalar_valuations=[1, 0])
        req["domain"]["profiles"] = [[0, 0]]
        result = tool.calculate(tool.validate(req))
        self.assertTrue(result["ledger_preserved"])
        self.assertFalse(result["domain_invariant"])
        self.assertEqual(result["generators"], [])

    def test_three_cycle_orientation(self):
        req = {"schema": 1, "p": 3, "weights": [2, -1, 4], "permutation": [1, 2, 0],
               "scalar_valuations": [1, -2, 3], "domain": {"kind": "finite_profiles", "profiles": [[5, 7, -2]]}}
        result = tool.calculate(tool.validate(req))
        self.assertEqual(result["image_profiles"], [[1, 6, 5]])
        before = 2*5 - 7 + 4*(-2)
        after = 2*1 - 6 + 4*5
        self.assertEqual(result["profile_shifts"], [after-before])

    def test_rejects_bool_composite_dimensions_and_bad_domain(self):
        for key, value in [("p", True), ("p", 4), ("weights", [True, 2]),
                           ("permutation", [0, 0]), ("scalar_valuations", [0])]:
            req = copy.deepcopy(BASE)
            req[key] = value
            with self.assertRaises(tool.InputError):
                tool.validate(req)
        for domain in [None, {"kind": "unprovided_IUT_domain"}]:
            req = copy.deepcopy(BASE)
            req["domain"] = domain
            with self.assertRaises(tool.Insufficient):
                tool.validate(req)

    def test_no_stale_success_after_missing_certificate(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parent) as tmp:
            root = Path(tmp)
            source, out = root / "input.json", root / "output"
            source.write_text(json.dumps(BASE), encoding="utf-8")
            result, code = tool.emit(source, out)
            self.assertEqual((result["status"], code), ("PROPOSED", 0))
            req = copy.deepcopy(BASE)
            del req["domain"]
            source.write_text(json.dumps(req), encoding="utf-8")
            result, code = tool.emit(source, out)
            self.assertEqual((result["status"], code), ("INSUFFICIENT", 2))
            self.assertEqual(json.loads((out/"manifest.json").read_text())["theorem_names"], [])
            self.assertNotIn("theorem", (out/"certificate.lean").read_text())


if __name__ == "__main__":
    unittest.main()
