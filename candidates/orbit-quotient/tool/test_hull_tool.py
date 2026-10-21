"""Independent finite-set oracles and input-contract regression tests (stdlib)."""
import itertools
import json
from pathlib import Path
import random
import tempfile
import unittest

import hull_tool as tool


class HullTests(unittest.TestCase):
    def test_original_two_three_four(self):
        data = tool.validate(dict(schema=1, p=2, N=1, thresholds=[0, 1], permutations=[[0, 1], [1, 0]]))
        result = tool.compute(data)
        box, union, hull = self.explicit_sets(data, result)
        self.assertEqual((len(box), len(union), len(hull)), (2, 3, 4))

    @staticmethod
    def explicit_sets(data, result):
        p, N, k = data['p'], data['N'], data['thresholds']
        box = set(itertools.product(*(range(0, p ** N, p ** v) for v in k)))
        union = set()
        # Independent forward assignment implements the left action directly.
        for perm in data['permutations']:
            for x in box:
                y = [None] * len(k)
                for j in range(len(k)):
                    y[perm[j]] = x[j]
                union.add(tuple(y))
        hull = set(itertools.product(*(range(0, p ** N, p ** v) for v in result['hull_thresholds'])))
        return box, union, hull

    def test_independent_set_oracle(self):
        rng = random.Random(20261021)
        all_perms = list(itertools.permutations(range(3)))
        for _ in range(100):
            perms = [list(p) for p in rng.sample(all_perms, rng.randint(1, 6))]
            data = tool.validate(dict(schema=1, p=2, N=2, thresholds=[rng.randrange(3) for _ in range(3)],
                                      permutations=perms, require_enlargement=False))
            result = tool.compute(data)
            box, union, hull = self.explicit_sets(data, result)
            actual_product = set(itertools.product(*({x[j] for x in union} for j in range(3))))
            self.assertEqual(hull, actual_product)
            self.assertTrue(union <= hull)
            self.assertEqual(len(box), 2 ** result['box_exponent'])
            self.assertEqual(len(hull), 2 ** result['hull_exponent'])
            self.assertIsNone(result['enlargement_exponent'])
            for j, witness in enumerate(result['witnesses']):
                self.assertEqual(perms[witness['permutation_index']][witness['source_coordinate']], j)
                self.assertEqual(result['hull_thresholds'][j], data['thresholds'][witness['source_coordinate']])

    def test_three_cycle_direction_and_no_identity(self):
        data = tool.validate(dict(schema=1, p=3, N=4, thresholds=[1, 2, 4],
                                  permutations=[[0, 1, 2], [1, 2, 0]]))
        result = tool.compute(data)
        self.assertEqual(result['hull_thresholds'], [1, 1, 2])
        self.assertEqual((result['box_exponent'], result['hull_exponent'], result['enlargement_exponent']), (5, 8, 3))
        data['permutations'] = [[1, 2, 0]]
        with self.assertRaises(tool.InputError):
            tool.validate(data)
        data['require_enlargement'] = False
        result = tool.compute(tool.validate(data))
        self.assertEqual(result['hull_thresholds'], [4, 1, 2])
        self.assertIsNone(result['cardinality']['ratio_exponent'])

    def test_type_domain_and_resource_rejections(self):
        base = dict(schema=1, p=2, N=1, thresholds=[0, 1], permutations=[[0, 1]])
        changes = [dict(schema=True), dict(p=True), dict(p=4), dict(N=-1), dict(N=10001),
                   dict(thresholds=[0, 2]), dict(thresholds=[]), dict(thresholds=[False, 1]),
                   dict(permutations=[]), dict(permutations=[[0, 0]]), dict(permutations=[[0]]),
                   dict(permutations=[[0, 2]]), dict(permutations=[[0, True]]),
                   dict(require_enlargement=1), dict(unrecognized=1)]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(tool.InputError):
                tool.validate(dict(base, **change))

    def test_emission_and_invalid_artifacts(self):
        runs = Path(__file__).resolve().parent / 'runs'
        runs.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as tmp:
            root = Path(tmp)
            source = root / 'input.json'
            source.write_text('{"schema":1,"p":5,"N":3,"thresholds":[0,2,3],"permutations":[[1,2,0]],"require_enlargement":false}')
            manifest = tool.emit(source, root / 'valid')
            self.assertEqual(manifest['status'], 'PROPOSED')
            self.assertEqual(manifest['result']['hull_thresholds'], [3, 0, 2])
            self.assertNotIn('HullToolCertificate.enlargement', manifest['theorem_names'])
            with self.assertRaises(tool.InputError):
                tool.emit(source, root / 'valid')
            source.write_text('{"schema":1,"schema":1}')
            with self.assertRaises(tool.InputError):
                tool.emit(source, root / 'bad')
            rejected = tool.invalid_artifacts(source, root / 'bad', 'duplicate key')
            self.assertEqual(rejected['status'], 'INVALID_INPUT')
            self.assertEqual(rejected['theorem_names'], [])
            for name in ('request.json', 'result.json', 'certificate.lean', 'manifest.json'):
                self.assertTrue((root / 'bad' / name).is_file())


if __name__ == '__main__':
    unittest.main()
