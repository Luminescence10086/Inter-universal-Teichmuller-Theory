"""Catalog DAG through helpers, kernel checks, and observed VS Code admission.
Pre/post hashes detect ordinary concurrent edits, not malicious restore races.
Editor receipts are observations, not anti-forgery attestations.
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
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def snapshot():
    # The local path dependencies must retain the recorded source identity.
    lock = json.loads((ROOT / 'external-lock.json').read_text(encoding='utf-8'))
    for package in lock['packages']:
        entry = Path(package['path'])
        head = subprocess.run(['git', '-C', str(entry), 'rev-parse', 'HEAD'],
            capture_output=True, text=True, check=True).stdout.strip()
        changes = subprocess.run(['git', '-C', str(entry), 'status', '--porcelain',
            '--untracked-files=no'], capture_output=True, text=True, check=True).stdout
        if head != package['commit'] or changes != package['tracked_changes']:
            raise RuntimeError('External source checkout changed: ' + package['name'])
    paths = [ROOT / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'LocalFieldAudit.lean', 'tools/verify.py', 'tools/query.py', 'tools/catalog.json',
        'tools/Export.lean', 'tools/Imports.lean', 'tools/EditorCheck.lean', 'external-lock.json']]
    paths += sorted((ROOT / 'LocalFieldAudit').rglob('*.lean'))
    paths += sorted((ROOT / '.vscode').glob('*.json'))
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}

def assert_snapshot(before, after):
    if before != after:
        raise RuntimeError('Verification inputs changed during/after checking')

def check_process(result, label):
    if result.returncode or result.stderr:
        raise RuntimeError(f'{label} failed or produced stderr: {result.stdout}\n{result.stderr}')

def run(args, label):
    result = subprocess.run(args, cwd=ROOT, text=True, encoding='utf-8',
        errors='strict', capture_output=True, timeout=300)
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

def runtime_snapshot(imports, prefix):
    paths = {Path(prefix) / 'bin' / name for name in ('lean.exe', 'lake.exe')}
    for row in imports:
        base = Path(row['path'])
        paths.add(base)
        for suffix in ('.private', '.server'):
            sidecar = Path(str(base) + suffix)
            if sidecar.exists():
                paths.add(sidecar)
    return {str(p.resolve()): digest(p) for p in sorted(paths)}

def receipt_valid(receipt, inputs, runtime, catalog):
    evidence_name = receipt.get('evidence', '')
    if not isinstance(evidence_name, str) or not re.fullmatch(
            r'verification/vscode-observation-round[1-9][0-9]*\.txt', evidence_name):
        return False
    evidence = ROOT / evidence_name
    return (receipt.get('schema') == 2 and receipt.get('input_sha256') == inputs
        and receipt.get('runtime_sha256') == runtime and evidence.exists()
        and receipt.get('evidence_sha256') == digest(evidence)
        and receipt.get('checked_targets') == sorted(item['id'] for item in catalog)
        and receipt.get('information_messages') == 2 * len(catalog))

def main():
    OUT.mkdir(exist_ok=True)
    TREE.mkdir(exist_ok=True)
    save(TREE / 'facts.json', {'status': 'verification_in_progress', 'nodes': [], 'edges': []})
    (TREE / 'graph.dot').write_text('digraph facts {}\n', encoding='utf-8')
    (TREE / 'index.md').write_text('# fact-tree\n\nVerification in progress.\n', encoding='utf-8')
    inputs = snapshot()
    catalog = json.loads((ROOT / 'tools/catalog.json').read_text(encoding='utf-8'))
    editor_source = (ROOT / 'tools/EditorCheck.lean').read_text(encoding='utf-8')
    expected_names = sorted(item['id'] for item in catalog)
    for command in ('check', 'print axioms'):
        actual_names = sorted(re.findall(r'^#' + command + r'\s+(\S+)\s*$', editor_source, re.M))
        if actual_names != expected_names:
            raise RuntimeError('Editor entry does not check every catalog target exactly once')
    sources = sorted({x['source'] for x in catalog})
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('lake is not on PATH')
    version = run([lake, 'env', 'lean', '--version'], 'version').strip()
    if 'version 4.34.0-rc2,' not in version:
        raise RuntimeError(f'Unexpected toolchain: {version}')
    # Keep Lake's dependency traces in sync with the Lean editor. A bare -o
    # compile produces valid OLeans but leaves setup-file reporting stale imports.
    build = run([lake, '--no-cache', '--wfail', 'build', 'LocalFieldAudit'], 'build')
    if 'warning:' in build.lower() or 'error:' in build.lower():
        raise RuntimeError('Build contains warning/error')
    prefix = run([lake, 'env', 'lean', '--print-prefix'], 'prefix').strip()
    imports = one_information(run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
        'tools/Imports.lean'], 'imports'))
    runtime = runtime_snapshot(imports, prefix)
    for path in sorted(p for p in inputs if p.endswith('.lean') and not p.startswith('tools/')):
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
    targets = {item['id'] for item in catalog}
    deps = {name: dependencies_via_helpers(name, by_id, targets) for name in targets}
    editor = run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
        'tools/EditorCheck.lean'], 'editor-cli')
    messages = [json.loads(line) for line in editor.splitlines() if line.strip()]
    if len(messages) != 2 * len(catalog) or any(m['severity'] != 'information' for m in messages):
        raise RuntimeError('Unexpected editor-entry CLI diagnostics')
    receipt_path = OUT / 'vscode-receipt.json'
    receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {}
    receipt_ok = receipt_valid(receipt, inputs, runtime, catalog)
    eligible = set()
    for item in catalog:
        name, path = item['id'], item['source']
        if set(by_id[name]['axioms']) - ALLOWED_AXIOMS:
            raise RuntimeError(f'Unapproved axioms: {name}')
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
            'scope': 'linear_algebra_and_padic_conditional_interface',
            'depends_on': sorted(deps[name]),
            'status': 'admitted' if name in admitted_ids else 'pending_vscode_or_dependency'})
    assert_snapshot(inputs, snapshot())
    assert_snapshot(runtime, runtime_snapshot(imports, prefix))
    common = {'schema': 2, 'generated_utc': datetime.now(timezone.utc).isoformat(),
        'lean': version, 'input_sha256': inputs, 'runtime_sha256': runtime,
        'trust': 'Installed Lean kernel/runtime and standard axioms; editor receipt is an observation, not an anti-forgery attestation.',
        'scope': 'Explicit catalog theorem DAG through project helper constants; external libraries are metadata, not fact-tree nodes.',
        'iut_cor312_proved': False, 'abc_proved': False}
    save(OUT / 'checked-inputs.json', {**common, 'checked_targets': sorted(targets), 'sources': sources})
    save(OUT / 'project-constants.json', rows)
    save(OUT / 'candidates.json', {**common, 'nodes': nodes})
    accepted = [row for row in nodes if row['id'] in admitted_ids]
    pending = len(nodes) - len(accepted)
    edges = [{'from': dep, 'to': row['id']} for row in accepted for dep in row['depends_on']]
    save(TREE / 'facts.json', {**common, 'status': 'checked', 'nodes': accepted,
        'edges': edges, 'pending_count': pending})
    lines = ['digraph facts {', '  rankdir=LR;']
    lines += [f'  "{row["id"]}";' for row in accepted]
    lines += [f'  "{edge["from"]}" -> "{edge["to"]}";' for edge in edges]
    (TREE / 'graph.dot').write_text('\n'.join(lines + ['}', '']), encoding='utf-8')
    index = ['# fact-tree', '', f'已准入 {len(accepted)} 个定理；待验收 {pending} 个。', '',
        '只包含线性代数及 p-adic 条件接口；Corollary 3.12 和 abc 均未证明。', '',
        'A→B：B 的 type/proof 经项目 helper 常量依赖最近的目录定理 A。外部库不是准入节点。', '',
        '| 定理 | 源文件 | 目录定理依赖 |', '|---|---|---|']
    index += [f'| `{r["id"]}` | `{r["source"]}` | {", ".join(r["depends_on"]) or "无"} |' for r in accepted]
    (TREE / 'index.md').write_text('\n'.join(index) + '\n', encoding='utf-8')
    print(f'Zero-diagnostic source checks passed. Admitted={len(accepted)}, pending={pending}, edges={len(edges)}.')

if __name__ == '__main__':
    main()
