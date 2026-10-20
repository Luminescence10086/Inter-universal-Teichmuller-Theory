"""Full input/runtime checks shared by the integration auditors.

These checks detect ordinary drift. Receipts remain observations in a writable
workspace, not tamper-proof certificates. No cross-toolchain proof is imported.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
from pathlib import Path


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def verifier(base):
    base = Path(base)
    integrated = base / 'tools/verify_integrated.py'
    path = integrated if integrated.exists() else base / 'tools/verify.py'
    spec = importlib.util.spec_from_file_location('fresh_' + base.name.replace('-', '_'), path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def assert_equal(expected, actual, label):
    if expected != actual:
        changed = sorted(k for k in expected.keys() | actual.keys()
                         if expected.get(k) != actual.get(k))
        raise RuntimeError(f'{label}: stale or incomplete snapshot: {changed[:20]}')


def validate_project(base, deep=True):
    """Require complete admission and recompute the input set, not just .lean keys."""
    base = Path(base)
    module = verifier(base)
    checked = load(base / 'verification/checked-inputs.json')
    tree = load(base / 'fact-tree/facts.json')
    assert_equal(checked['input_sha256'], module.snapshot(), str(base))
    assert_equal(checked['input_sha256'], tree.get('input_sha256', {}), 'tree inputs')
    if hasattr(module, 'dependency_snapshot'):
        assert_equal(checked['dependency_sha256'], module.dependency_snapshot(), 'dependencies')
        assert_equal(checked['dependency_sha256'], tree.get('dependency_sha256', {}),
                     'tree dependencies')
    catalog = load(base / 'tools/catalog.json')
    targets = sorted(row['id'] for row in catalog)
    if (tree.get('status') != 'checked' or tree.get('pending_count') != 0
            or checked.get('checked_targets') != targets
            or sorted(row['id'] for row in tree['nodes']) != targets
            or any(row.get('status') != 'admitted' for row in tree['nodes'])):
        raise RuntimeError(f'{base}: not fully admitted, or stale target set')
    expected_edges = {(dep, row['id']) for row in tree['nodes'] for dep in row['depends_on']}
    actual_edges = {(edge['from'], edge['to']) for edge in tree['edges']}
    if (expected_edges != actual_edges or len(set(targets)) != len(targets)
            or any(a not in targets or b not in targets for a, b in actual_edges)):
        raise RuntimeError(f'{base}: malformed fact DAG')
    if deep:
        imports_result = load(base / 'verification/imports.json')
        prefix_result = load(base / 'verification/prefix.json')
        imports = module.one_information(imports_result['stdout'])
        prefix = prefix_result['stdout'].strip()
        # Re-discover optional sidecars; hashing recorded paths alone misses additions.
        actual_runtime = module.runtime_snapshot(imports, prefix)
        assert_equal(checked['runtime_sha256'], actual_runtime, 'runtime')
        assert_equal(checked['runtime_sha256'], tree.get('runtime_sha256', {}), 'tree runtime')
    rows = load(base / 'verification/project-constants.json')
    export = load(base / 'verification/export.json')
    if export.get('exit_code') != 0 or export.get('stderr'):
        raise RuntimeError(f'{base}: failed export')
    if rows != module.one_information(export['stdout']):
        raise RuntimeError(f'{base}: project constants disagree with recorded Lean export')
    return {row['id']: row for row in rows}, checked


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()
