"""Negative regression fixtures for the integration auditors, not proof receipts."""
import unittest
from freshness import assert_equal
from semantic_lock import fingerprint, diff


class DriftTests(unittest.TestCase):
    def test_config_changes_are_rejected(self):
        original = {'lean-toolchain': 'a', 'lake-manifest.json': 'b', 'Proof.lean': 'c'}
        for name in original:
            changed = {**original, name: 'changed'}
            with self.subTest(name=name), self.assertRaises(RuntimeError):
                assert_equal(original, changed, 'fixture')

    def test_input_set_additions_and_removals_are_rejected(self):
        for changed in ({'A.lean': 'a', 'New.lean': 'n'}, {}):
            with self.assertRaises(RuntimeError):
                assert_equal({'A.lean': 'a'}, changed, 'fixture')

    def test_identical_predicate_types_do_not_hide_body_changes(self):
        row = {'id': 'N.P', 'kind': 'definition', 'module': 'N',
               'statement': 'Nat → Prop', 'axioms': []}
        a = fingerprint(row, {'N.P': 'fun n => n = 0'})
        b = fingerprint(row, {'N.P': 'fun n => n = 1'})
        self.assertEqual(a['statement_sha256'], b['statement_sha256'])
        self.assertEqual(diff({'N.P': a}, {'N.P': b}), (['N.P'], [], []))

    def test_module_and_axiom_changes_are_rejected(self):
        row = {'id': 'N.t', 'kind': 'theorem', 'module': 'N',
               'statement': 'True', 'axioms': []}
        old = fingerprint(row, {})
        for update in ({'module': 'Other'}, {'axioms': ['sorryAx']}):
            new = fingerprint({**row, **update}, {})
            self.assertEqual(diff({'t': old}, {'t': new})[0], ['t'])

    def test_namespaces_are_not_erased(self):
        row = {'id': 't', 'kind': 'theorem', 'module': 'N',
               'statement': 'N.P x', 'axioms': []}
        self.assertNotEqual(fingerprint(row, {}),
                            fingerprint({**row, 'statement': 'M.P x'}, {}))


if __name__ == '__main__':
    unittest.main()
