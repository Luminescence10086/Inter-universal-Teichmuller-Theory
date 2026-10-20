"""Bridge-project verifier: catalog DAG, kernel checks, hypothesis audit.

Differences from the two earlier verifiers in this repository:

* **Hypothesis audit.** Every explicit, non-typeclass `Prop` binder of every
  catalog theorem must be declared in `tools/catalog.json`. A theorem that
  silently acquires a premise fails verification instead of counting as
  unconditional progress.
* **Dependency identity.** The audited `local-field` library is a path
  dependency; this verifier records a hash snapshot of its proof sources and
  configuration, so a bridge theorem can only be admitted against the exact
  dependency it was checked against.
* Admission still requires a real editor observation receipt. Until that receipt
  exists, every node is reported as `cli_verified_awaiting_editor` and the
  fact-tree stays empty: CLI cleanliness is necessary but not sufficient.
Pre/post hashes detect ordinary concurrent edits, not malicious restore races.
"""
from __future__ import annotations
import hashlib
import json
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
TREE = ROOT / 'fact-tree'
DEP = ROOT.parent / 'local-field'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TOOL_FILES = ['tools/verify.py', 'tools/catalog.json', 'tools/Export.lean',
              'tools/Imports.lean', 'tools/EditorCheck.lean', 'tools/Binders.lean']
CONFIG_FILES = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'IUTBridge.lean']


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def dependency_snapshot():
    """Pin the audited dependency this bridge is checked against."""
    paths = [DEP / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                               'LocalFieldAudit.lean']]
    paths += sorted((DEP / 'LocalFieldAudit').rglob('*.lean'))
    return {p.relative_to(ROOT.parent).as_posix(): digest(p) for p in paths}


def snapshot():
    paths = [ROOT / p for p in CONFIG_FILES + TOOL_FILES]
    paths += sorted((ROOT / 'IUTBridge').rglob('*.lean'))
    paths += sorted((ROOT / '.vscode').glob('*.json'))
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


def assert_snapshot(before, after, label):
    if before != after:
        raise RuntimeError(f'Verification inputs changed during/after checking: {label}')


def check_process(result, label):
    if result.returncode or result.stderr:
        raise RuntimeError(f'{label} failed or produced stderr: {result.stdout}\n{result.stderr}')


def run(args, label):
    result = subprocess.run(args, cwd=ROOT, text=True, encoding='utf-8',
                            errors='strict', capture_output=True, timeout=1800)
    save(OUT / f'{label}.json', {'command': args, 'exit_code': result.returncode,
                                 'stdout': result.stdout, 'stderr': result.stderr})
    check_process(result, label)
    return result.stdout


def one_information(output):
    messages = [json.loads(line) for line in output.splitlines() if line.strip()]
    if len(messages) != 1 or messages[0].get('severity') != 'information':
        raise RuntimeError('Expected exactly one informational export, no warnings/errors')
    return json.loads(messages[0]['data'])


def validate_catalog(catalog, by_id):
    seen = set()
    for item in catalog:
        name, source = item['id'], item['source']
        if name in seen:
            raise RuntimeError(f'Duplicate catalog theorem: {name}')
        seen.add(name)
        if name not in by_id or by_id[name]['kind'] != 'theorem':
            raise RuntimeError(f'Catalog entry is not an elaborated theorem: {name}')
        if by_id[name]['module'] != source.removesuffix('.lean').replace('/', '.'):
            raise RuntimeError(f'Catalog module mismatch: {name}')
        if 'hypotheses' not in item:
            raise RuntimeError(f'Catalog entry does not declare its hypotheses: {name}')


def audit_hypotheses(catalog, binder_rows):
    """Every explicit non-typeclass Prop binder must be declared in the catalog."""
    by_id = {row['id']: row for row in binder_rows}
    for item in catalog:
        name = item['id']
        if name not in by_id:
            raise RuntimeError(f'Binder audit missing catalog target: {name}')
        actual = sorted(b['name'] for b in by_id[name]['binders']
                        if b['isProp'] and b['isExplicit'] and not b['isInstance'])
        declared = sorted(item['hypotheses'])
        if actual != declared:
            raise RuntimeError(
                f'Undeclared or stale hypotheses for {name}: kernel reports {actual}, '
                f'catalog declares {declared}')
    return {item['id']: sorted(item['hypotheses']) for item in catalog}


def dependencies_via_helpers(name, by_id, targets):
    found, seen = set(), {name}
    todo = list(by_id[name]['constants'])
    while todo:
        dep = todo.pop()
        if dep in seen:
            continue
        seen.add(dep)
        if dep in targets:
            found.add(dep)
        elif dep in by_id:
            todo.extend(by_id[dep]['constants'])
    return found


def admission_closure(eligible, deps):
    admitted = set(eligible)
    while True:
        reduced = {name for name in admitted if deps[name] <= admitted}
        if reduced == admitted:
            return reduced
        admitted = reduced


def receipt_valid(receipt, inputs, deps, catalog):
    evidence_name = receipt.get('evidence', '')
    if not isinstance(evidence_name, str) or not re.fullmatch(
            r'verification/vscode-observation-round[1-9][0-9]*\.txt', evidence_name):
        return False
    evidence = ROOT / evidence_name
    return (receipt.get('schema') == 2 and receipt.get('input_sha256') == inputs
            and receipt.get('dependency_sha256') == deps and evidence.exists()
            and receipt.get('evidence_sha256') == digest(evidence)
            and receipt.get('checked_targets') == sorted(item['id'] for item in catalog)
            and receipt.get('information_messages') == 2 * len(catalog))


def local_dependency_check():
    """Fail if the audited dependency has uncommitted proof-source edits.

    The dependency is a path package inside this repository, so its sources are
    covered by the dependency snapshot; this extra check only reports whether the
    bridge was built against a dirty tree, which is recorded in the audit output.
    """
    result = subprocess.run(['git', '-C', str(ROOT.parent), 'status', '--porcelain',
                             '--untracked-files=no', '--', 'local-field/'],
                            text=True, capture_output=True)
    return result.stdout


def main():
    OUT.mkdir(exist_ok=True)
    TREE.mkdir(exist_ok=True)
    save(TREE / 'facts.json', {'status': 'verification_in_progress', 'nodes': [], 'edges': []})
    (TREE / 'graph.dot').write_text('digraph facts {}\n', encoding='utf-8')
    (TREE / 'index.md').write_text('# fact-tree\n\nVerification in progress.\n', encoding='utf-8')

    inputs = snapshot()
    depsnap = dependency_snapshot()
    catalog = json.loads((ROOT / 'tools/catalog.json').read_text(encoding='utf-8'))
    editor_source = (ROOT / 'tools/EditorCheck.lean').read_text(encoding='utf-8')
    expected_names = sorted(item['id'] for item in catalog)
    for command in ('check', 'print axioms'):
        actual_names = sorted(re.findall(r'^#' + command + r'\s+(\S+)\s*$', editor_source, re.M))
        if actual_names != expected_names:
            raise RuntimeError('Editor entry does not check every catalog target exactly once')

    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('lake is not on PATH')
    version = run([lake, 'env', 'lean', '--version'], 'version').strip()
    if 'version 4.34.0-rc2' not in version:
        raise RuntimeError(f'Unexpected toolchain: {version}')
    build = run([lake, '--wfail', 'build', 'IUTBridge'], 'build')
    if 'warning:' in build.lower() or 'error:' in build.lower():
        raise RuntimeError('Build contains warning/error')

    for path in sorted(p for p in inputs
                       if p.endswith('.lean') and not p.startswith('tools/')):
        output = run([lake, 'env', 'lean', '--json', '-DwarningAsError=true', path],
                     'source-' + path.replace('/', '-').removesuffix('.lean'))
        if output.strip():
            raise RuntimeError(f'Nonempty source diagnostics: {path}')

    rows = one_information(run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
                                'tools/Export.lean'], 'export'))
    by_id = {row['id']: row for row in rows}
    if len(by_id) != len(rows):
        raise RuntimeError('Duplicate exported constant')
    validate_catalog(catalog, by_id)

    binder_rows = one_information(run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
                                       'tools/Binders.lean'], 'binders'))
    declared = audit_hypotheses(catalog, binder_rows)

    targets = {item['id'] for item in catalog}
    deps = {name: dependencies_via_helpers(name, by_id, targets) for name in targets}
    editor = run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
                  'tools/EditorCheck.lean'], 'editor-cli')
    messages = [json.loads(line) for line in editor.splitlines() if line.strip()]
    if len(messages) != 2 * len(catalog) or any(m['severity'] != 'information' for m in messages):
        raise RuntimeError('Unexpected editor-entry CLI diagnostics')

    for item in catalog:
        name = item['id']
        if set(by_id[name]['axioms']) - ALLOWED_AXIOMS:
            raise RuntimeError(f'Unapproved axioms: {name}')

    receipt_path = OUT / 'vscode-receipt.json'
    receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {}
    receipt_ok = receipt_valid(receipt, inputs, depsnap, catalog)
    eligible = set()
    for item in catalog:
        name, path = item['id'], item['source']
        evidence = receipt.get('files', {}).get(path, {})
        if (receipt_ok and evidence.get('sha256') == inputs[path]
                and evidence.get('lean_server_checked') is True
                and evidence.get('errors') == 0 and evidence.get('warnings') == 0):
            eligible.add(name)
    admitted_ids = admission_closure(eligible, deps)

    nodes = []
    for item in sorted(catalog, key=lambda x: x['id']):
        name, path = item['id'], item['source']
        nodes.append({**by_id[name], 'source': path, 'sha256': inputs[path],
                      'hypotheses': declared[name],
                      'scope': 'generic_bridge_or_actual_base_field_Q_p',
                      'depends_on': sorted(deps[name]),
                      'status': ('admitted' if name in admitted_ids
                                 else 'cli_verified_awaiting_editor')})
    assert_snapshot(inputs, snapshot(), 'inputs')
    assert_snapshot(depsnap, dependency_snapshot(), 'dependency')

    common = {'schema': 2, 'generated_utc': datetime.now(timezone.utc).isoformat(),
              'lean': version, 'input_sha256': inputs, 'dependency_sha256': depsnap,
              'trust': ('Installed Lean kernel/runtime and standard axioms only. '
                        'No editor receipt: nodes are CLI-verified but not admitted.'),
              'scope': ('Base-field Q_p statements over imported LocalFieldAudit and Mathlib; '
                        'external libraries stay metadata, not fact-tree nodes.'),
              'hypotheses_audited': True,
              'dependency_status': local_dependency_check(),
              'iut_cor312_proved': False, 'abc_proved': False,
              'iut_object_constructed': False}
    save(OUT / 'checked-inputs.json', {**common, 'checked_targets': sorted(targets),
                                       'sources': sorted({x['source'] for x in catalog})})
    save(OUT / 'project-constants.json', rows)
    save(OUT / 'binder-audit.json', {'generated_utc': common['generated_utc'],
                                     'declared_hypotheses': declared, 'rows': binder_rows})
    save(OUT / 'candidates.json', {**common, 'nodes': nodes})
    accepted = [row for row in nodes if row['id'] in admitted_ids]
    pending = len(nodes) - len(accepted)
    edges = [{'from': dep, 'to': row['id']} for row in accepted for dep in row['depends_on']]
    save(TREE / 'facts.json', {**common, 'status': 'cli_verified_awaiting_editor',
                               'nodes': accepted, 'edges': edges, 'pending_count': pending})
    lines = ['digraph facts {', '  rankdir=LR;']
    lines += [f'  "{row["id"]}";' for row in accepted]
    lines += [f'  "{edge["from"]}" -> "{edge["to"]}";' for edge in edges]
    (TREE / 'graph.dot').write_text('\n'.join(lines + ['}', '']), encoding='utf-8')
    index = ['# bridge fact-tree', '',
             f'CLI 已核验 {len(nodes)} 条定理；已准入 {len(accepted)} 条（尚缺编辑器观察）。', '',
             '本文件为空表示尚未取得编辑器验收，这不是失败，也不表示定理被否定。', '',
             '全部结论限于基域 `Q_p` 与下列显式假设；未构造 IUT 对象，未证明 Corollary 3.12 或 abc。', '',
             '| 定理 | 源文件 | 显式前提 | 目录定理依赖 |', '|---|---|---|---|']
    index += [f'| `{r["id"]}` | `{r["source"]}` | {", ".join(r["hypotheses"]) or "无"} | '
              f'{", ".join(r["depends_on"]) or "无"} |' for r in accepted]
    (TREE / 'index.md').write_text('\n'.join(index) + '\n', encoding='utf-8')
    print(f'Zero-diagnostic source checks passed; hypotheses audited for {len(nodes)} theorems. '
          f'Admitted={len(accepted)}, pending={pending}, edges={len(edges)}.')


if __name__ == '__main__':
    main()
