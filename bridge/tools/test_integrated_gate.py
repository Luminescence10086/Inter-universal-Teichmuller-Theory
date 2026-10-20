"""Focused fail-closed tests for the integrated verifier's freshness gates."""
import importlib.util
import tempfile
import unittest
import json
from pathlib import Path
from unittest.mock import patch


VERIFY_PATH = Path(__file__).with_name('verify_integrated.py')
SPEC = importlib.util.spec_from_file_location('verify_integrated', VERIFY_PATH)
verify = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify)


class FreshnessGateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=Path(__file__).parent)
        self.workspace = Path(self.temp.name)
        self.root = self.workspace / 'bridge'
        (self.root / 'IUTBridge').mkdir(parents=True)
        (self.root / 'tools').mkdir()
        (self.workspace / 'tools').mkdir()
        for rel, content in {
            'lean-toolchain': 'leanprover/lean4:v4.34.0-rc2\n',
            'lakefile.toml': 'package test\n',
            'lake-manifest.json': '{}\n',
            'IUTBridge.lean': 'import IUTBridge.A\n',
            'IUTBridge/A.lean': 'theorem a : True := by trivial\n',
            'tools/catalog.json': '[]\n',
            'tools/EditorCheck.lean': '-- check target\n',
        }.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding='utf-8')

    def tearDown(self):
        self.temp.cleanup()

    def test_toolchain_catalog_and_new_source_change_input_identity(self):
        before = verify.project_snapshot(self.root)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v5\n', encoding='utf-8')
        self.assertNotEqual(before, verify.project_snapshot(self.root), 'toolchain edit passed')

        before = verify.project_snapshot(self.root)
        (self.root / 'tools/catalog.json').write_text('[{"id":"changed"}]\n', encoding='utf-8')
        self.assertNotEqual(before, verify.project_snapshot(self.root), 'catalog edit passed')

        before = verify.project_snapshot(self.root)
        (self.root / 'IUTBridge/NewTheorem.lean').write_text('theorem b : True := by trivial\n',
                                                               encoding='utf-8')
        self.assertNotEqual(before, verify.project_snapshot(self.root), 'new source passed')

    def test_runtime_edit_and_new_sidecar_change_runtime_identity(self):
        prefix = self.workspace / 'lean'
        (prefix / 'bin').mkdir(parents=True)
        (prefix / 'bin' / 'lean.exe').write_bytes(b'lean-a')
        (prefix / 'bin' / 'lake.exe').write_bytes(b'lake-a')
        olean = self.workspace / 'Mathlib' / 'A.olean'
        olean.parent.mkdir()
        olean.write_bytes(b'olean-a')
        imports = [{'module': 'Mathlib.A', 'path': str(olean)}]

        before = verify.runtime_snapshot(imports, prefix)
        (olean.parent / 'A.olean.server').write_bytes(b'server-sidecar')
        after = verify.runtime_snapshot(imports, prefix)
        self.assertNotEqual(before, after, 'new runtime sidecar passed')

        before = after
        (prefix / 'bin' / 'lean.exe').write_bytes(b'lean-b')
        self.assertNotEqual(before, verify.runtime_snapshot(imports, prefix),
                            'Lean runtime edit passed')

    def test_external_config_uses_manifest_lean_or_toml_filename(self):
        package = self.workspace / 'external'
        package.mkdir()
        (package / 'lakefile.lean').write_text('import Lake\n', encoding='utf-8')
        lock = self.workspace / 'external-lock.json'
        lock.write_text(json.dumps({'packages': [{'name': 'fixture', 'path': str(package),
            'commit': 'abc', 'tracked_changes': '',
            'config_sha256': verify.digest(package / 'lakefile.lean')}]}), encoding='utf-8')
        (self.workspace / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'name': 'fixture', 'configFile': 'lakefile.lean'}]}), encoding='utf-8')
        from types import SimpleNamespace
        def git_fixture(command, **kwargs):
            return SimpleNamespace(stdout='abc\n' if 'rev-parse' in command else '')
        with patch.object(verify.subprocess, 'run', side_effect=git_fixture):
            self.assertEqual(verify.external_git_identity(lock)['packages'][0]['commit'], 'abc')
            (package / 'lakefile.lean').write_text('changed', encoding='utf-8')
            with self.assertRaises(RuntimeError):
                verify.external_git_identity(lock)

    def test_receipt_binds_full_runtime_and_editor_file_observation(self):
        verification = self.root / 'verification'
        verification.mkdir()
        evidence = verification / 'vscode-observation-round1.txt'
        evidence.write_text('observed in editor\n', encoding='utf-8')
        catalog = [{'id': 'IUTBridge.A.a', 'source': 'IUTBridge/A.lean'}]
        inputs = {'IUTBridge/A.lean': 'source-hash',
                  'tools/EditorCheck.lean': 'editor-hash'}
        dependencies = {'dependency': 'dependency-hash'}
        runtime = {'C:/lean/bin/lean.exe': 'runtime-hash'}
        receipt = {
            'schema': 3,
            'evidence': 'verification/vscode-observation-round1.txt',
            'input_sha256': inputs,
            'dependency_sha256': dependencies,
            'runtime_sha256': runtime,
            'evidence_sha256': verify.digest(evidence),
            'checked_targets': ['IUTBridge.A.a'],
            'information_messages': 2,
            'files': {
                'IUTBridge/A.lean': {'sha256': 'source-hash', 'lean_server_checked': True,
                                    'errors': 0, 'warnings': 0},
                'tools/EditorCheck.lean': {'sha256': 'editor-hash',
                    'lean_server_checked': True, 'errors': 0, 'warnings': 0,
                    'information_messages': 2},
            },
        }
        with patch.object(verify, 'ROOT', self.root):
            self.assertTrue(verify.receipt_valid(receipt, inputs, dependencies, runtime, catalog))
            receipt['schema'] = 2
            self.assertFalse(verify.receipt_valid(receipt, inputs, dependencies, runtime, catalog))
            receipt['schema'] = 3
            self.assertFalse(verify.receipt_valid(receipt, inputs, dependencies,
                                                  {**runtime, 'new': 'artifact'}, catalog),
                             'receipt with stale runtime identity passed')
            receipt['files']['tools/EditorCheck.lean']['lean_server_checked'] = False
            self.assertFalse(verify.receipt_valid(receipt, inputs, dependencies, runtime, catalog),
                             'receipt without EditorCheck server observation passed')


if __name__ == '__main__':
    unittest.main()
