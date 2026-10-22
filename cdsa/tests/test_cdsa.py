"""Tests for the CDS-A layers: compile budgets, envelope schema, hash chain, gates."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from cdsa import core, engine  # noqa: E402

GOOD_SPEC = {
    'goal': 'demo',
    'budgets': {'max_nodes': 3, 'max_parallel': 2},
    'nodes': [
        {'id': 'A', 'role': 'generate',
         'executor': {'kind': 'command', 'argv': ['python', '-B', '-c', 'print(1)']},
         'allowed_paths': [], 'claim_template': 'node A ran (exit {code})',
         'dissent_template': 'printing 1 proves nothing about the goal', 'confidence': 0.7,
         'timeout': 60},
        {'id': 'B', 'role': 'verify',
         'executor': {'kind': 'command', 'argv': ['python', '-B', '-c', 'print(2)']},
         'allowed_paths': [], 'claim_template': 'node B ran (exit {code})',
         'dissent_template': 'verification here only checks the exit code', 'confidence': 0.8,
         'timeout': 60},
    ],
    'edges': [{'from': 'A', 'to': 'B',
               'verify': ['ancestors_green', 'envelope_valid', 'evidence_resolves',
                          'dissent_present']}],
}


def spec_with(**overrides):
    spec = json.loads(json.dumps(GOOD_SPEC))
    spec.update(overrides)
    return spec


class CompileLayer(unittest.TestCase):
    def test_valid_spec_compiles_with_stable_digest(self):
        first, problems = engine.compile_spec(GOOD_SPEC)
        second, _ = engine.compile_spec(json.loads(json.dumps(GOOD_SPEC)))
        self.assertEqual(problems, [])
        self.assertEqual(first['spec_digest'], second['spec_digest'])
        self.assertEqual(first['topo'], ['A', 'B'])

    def test_cycle_is_rejected(self):
        spec = spec_with(edges=[{'from': 'A', 'to': 'B', 'verify': []},
                                {'from': 'B', 'to': 'A', 'verify': []}])
        _, problems = engine.compile_spec(spec)
        self.assertTrue(any('cycle' in p for p in problems), problems)

    def test_node_budget_is_enforced(self):
        spec = spec_with(budgets={'max_nodes': 1, 'max_parallel': 1})
        _, problems = engine.compile_spec(spec)
        self.assertTrue(any('budget exceeded' in p for p in problems), problems)

    def test_missing_dissent_is_a_compile_error(self):
        spec = json.loads(json.dumps(GOOD_SPEC))
        del spec['nodes'][0]['dissent_template']
        _, problems = engine.compile_spec(spec)
        self.assertTrue(any('dissent_template' in p for p in problems), problems)

    def test_undeclared_node_and_edge_keys_are_rejected(self):
        spec = json.loads(json.dumps(GOOD_SPEC))
        spec['nodes'][0]['chat'] = 'free negotiation'
        spec['edges'][0]['negotiate'] = True
        _, problems = engine.compile_spec(spec)
        self.assertTrue(any('undeclared node keys' in p for p in problems), problems)
        self.assertTrue(any('undeclared keys' in p for p in problems), problems)


class EnvelopeLayer(unittest.TestCase):
    def good(self):
        return {'claim_id': 'c1', 'claim': 'a sufficiently long claim', 'evidence': [
                    {'kind': 'file', 'ref': 'README.md'}],
                'confidence': 0.7, 'artifactRef': '', 'dissent': ['objection'],
                'producer': 'N', 'spec_digest': 'd' * 64, 'version': 'v1', 'kind': 'command'}

    def test_valid_envelope(self):
        self.assertEqual(core.validate_envelope(self.good()), [])

    def test_empty_dissent_is_invalid(self):
        env = self.good()
        env['dissent'] = []
        self.assertTrue(any('dissent' in p for p in core.validate_envelope(env)))

    def test_conversation_field_is_rejected(self):
        env = self.good()
        env['conversation'] = 'chat'
        self.assertTrue(any('undeclared' in p for p in core.validate_envelope(env)))

    def test_confidence_bounds(self):
        env = self.good()
        env['confidence'] = 1.5
        self.assertTrue(any('confidence' in p for p in core.validate_envelope(env)))


class StateLayer(unittest.TestCase):
    def test_append_requires_lock_and_chain_verifies(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = core.EventLog(tmp)
            with self.assertRaises(RuntimeError):
                log.append('envelope', {'x': 1})
            log.acquire('test')
            log.append('envelope', {'x': 1})
            log.append('gate', {'edge': 'a->b', 'color': 'green', 'reasons': []})
            log.release()
            self.assertIsNone(log.verify_chain())
            self.assertEqual(len(log._lines()), 2)

    def test_tampering_breaks_the_chain(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = core.EventLog(tmp)
            log.acquire('test')
            log.append('envelope', {'x': 1})
            log.release()
            text = log.path.read_text(encoding='utf-8').replace('"x":1', '"x":2')
            log.path.write_text(text, encoding='utf-8')
            self.assertIsNotNone(log.verify_chain())


class GateLayer(unittest.TestCase):
    def envelope(self, **overrides):
        env = {'claim_id': 'c', 'claim': 'a sufficiently long claim', 'evidence': [
                   {'kind': 'file', 'ref': 'README.md'}],
               'confidence': 0.7, 'artifactRef': '', 'dissent': ['objection'],
               'producer': 'N', 'spec_digest': 'd' * 64, 'version': 'v1', 'kind': 'command'}
        env.update(overrides)
        return env

    def node(self, **overrides):
        node = {'id': 'N', 'role': 'generate', 'allowed_paths': [], 'confidence_floor': 0.6}
        node.update(overrides)
        return node

    def test_green(self):
        color, _ = engine.gate_envelope(self.envelope(), self.node(), ROOT)
        self.assertEqual(color, 'green')

    def test_forbidden_phrase_is_red(self):
        color, reasons = engine.gate_envelope(
            self.envelope(claim='this proves abc and Cor 3.12'), self.node(
                forbidden_in_claim=['proves abc']), ROOT)
        self.assertEqual(color, 'red')
        self.assertTrue(any('forbidden' in r for r in reasons))

    def test_low_confidence_is_yellow(self):
        color, _ = engine.gate_envelope(self.envelope(confidence=0.2), self.node(), ROOT)
        self.assertEqual(color, 'yellow')

    def test_single_evidence_kind_yellow_for_verify_role(self):
        color, _ = engine.gate_envelope(self.envelope(), self.node(role='verify'), ROOT)
        self.assertEqual(color, 'yellow')

    def test_arbiter_rejects_without_two_evidence_kinds(self):
        color, _ = engine.arbitrate(self.envelope(confidence=0.7), ROOT)
        self.assertEqual(color, 'red')

    def test_arbiter_accepts_with_two_resolved_kinds(self):
        env = self.envelope(evidence=[{'kind': 'file', 'ref': 'README.md'},
                                      {'kind': 'command', 'ref': 'README.md'}])
        color, _ = engine.arbitrate(env, ROOT)
        self.assertEqual(color, 'green')

    def test_missing_evidence_file_is_red(self):
        color, reasons = engine.gate_envelope(
            self.envelope(evidence=[{'kind': 'file', 'ref': 'no/such/file.txt'}]),
            self.node(), ROOT)
        self.assertEqual(color, 'red')
        self.assertTrue(any('missing' in r for r in reasons))

    def test_downstream_closure(self):
        compiled, _ = engine.compile_spec(GOOD_SPEC)
        self.assertEqual(engine.downstream_closure(compiled, 'A'), ['A', 'B'])


class EndToEnd(unittest.TestCase):
    def test_two_node_run_is_green_and_verifies(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / 'repo'
            repo.mkdir()
            compiled, problems = engine.compile_spec(GOOD_SPEC)
            self.assertEqual(problems, [])
            state, report = engine.run(compiled, repo, Path(tmp) / 'run')
            self.assertEqual(report['waiting'], [])
            self.assertEqual(sorted(state['admitted']), ['A', 'B'])
            self.assertEqual(state['gates']['A:self'], 'green')
            self.assertEqual(state['gates']['B:self'], 'green')
            self.assertEqual(state['gates']['A->B'], 'green')
            final = engine.final_answer(compiled, repo, Path(tmp) / 'run')
            self.assertEqual(final['status'], 'PASS', final['problems'])
            self.assertTrue(final['chain_ok'])

    def test_red_parent_rolls_back_only_its_closure(self):
        spec = json.loads(json.dumps(GOOD_SPEC))
        spec['nodes'][0]['executor']['argv'] = ['python', '-B', '-c', 'raise SystemExit(3)']
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / 'repo'
            repo.mkdir()
            compiled, problems = engine.compile_spec(spec)
            self.assertEqual(problems, [])
            state, report = engine.run(compiled, repo, Path(tmp) / 'run')
            self.assertEqual(state['gates'].get('A:self'), 'red')
            self.assertNotIn('A', state['admitted'])
            self.assertNotIn('B', state['admitted'])
            self.assertEqual(state['gates'].get('A->B'), 'red')
            final = engine.final_answer(compiled, repo, Path(tmp) / 'run')
            self.assertEqual(final['status'], 'FAIL')


if __name__ == '__main__':
    unittest.main(verbosity=2)
