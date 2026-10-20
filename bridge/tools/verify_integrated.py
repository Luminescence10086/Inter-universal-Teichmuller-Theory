"""Integrated bridge verifier with schema-3, source/dependency/runtime binding.

This verifier writes the standard bridge verification and fact-tree outputs.
An editor receipt records an observation; it is not an anti-forgery attestation.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parent
DEP = WORKSPACE / 'local-field'
OUT = ROOT / 'verification'
TREE = ROOT / 'fact-tree'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path: Path) -> str:
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def _files(root: Path, patterns: Iterable[str]) -> set[Path]:
    found: set[Path] = set()
    for pattern in patterns:
        found.update(root.glob(pattern))
    return {p for p in found if p.is_file()}


def project_snapshot(root: Path = ROOT) -> dict[str, str]:
    """Hash all project Lean sources, project config/tools, and audit inputs."""
    root = Path(root).resolve()
    workspace = root.parent
    paths = {root / p for p in (
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'IUTBridge.lean')}
    paths |= _files(root / 'IUTBridge', ('**/*.lean',))
    paths |= _files(root / 'tools', ('*.lean', '*.py', '*.json'))
    # Root audit tools participate in freshness and semantic locks as well.
    paths |= _files(workspace / 'tools', ('*.lean', '*.py', '*.json'))
    paths |= _files(root / '.vscode', ('*.json',))
    paths |= _files(workspace / '.vscode', ('*.json',))
    def key(path: Path) -> str:
        resolved = path.resolve()
        try:
            return resolved.relative_to(root).as_posix()
        except ValueError:
            return '@workspace/' + resolved.relative_to(workspace).as_posix()
    return dict(sorted({key(p): digest(p) for p in paths}.items()))


# Stable alias used by the freshness/export tools.
def snapshot() -> dict[str, str]:
    return project_snapshot()


def external_git_identity(lock_path: Path) -> dict:
    lock = json.loads(Path(lock_path).read_text(encoding='utf-8'))
    manifest = json.loads((Path(lock_path).parent / 'lake-manifest.json').read_text(encoding='utf-8'))
    config_files = {p['name']: p['configFile'] for p in manifest['packages']}
    identities = []
    for package in lock['packages']:
        entry = Path(package['path'])
        head = subprocess.run(['git', '-C', str(entry), 'rev-parse', 'HEAD'],
                              capture_output=True, text=True, check=True).stdout.strip()
        changes = subprocess.run(['git', '-C', str(entry), 'status', '--porcelain',
                                  '--untracked-files=no'], capture_output=True,
                                 text=True, check=True).stdout
        # Packages may use lakefile.lean; use the resolved manifest rather than
        # guessing a TOML filename (notably proofwidgets and Mathlib use Lean).
        config_path = entry / config_files[package['name']]
        if head != package['commit'] or changes != package['tracked_changes']:
            raise RuntimeError('External source checkout changed: ' + package['name'])
        config_sha = digest(config_path)
        if package.get('config_sha256') and config_sha != package['config_sha256']:
            raise RuntimeError('External package config changed: ' + package['name'])
        identities.append({'name': package['name'], 'path': str(entry.resolve()),
                           'commit': head, 'tracked_changes': changes,
                           'config_sha256': config_sha})
    return {'lock_sha256': digest(lock_path), 'packages': identities}


def dependency_snapshot(dep: Path = DEP) -> dict[str, str]:
    dep = Path(dep).resolve()
    paths = {dep / p for p in (
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'LocalFieldAudit.lean', 'external-lock.json')}
    paths |= _files(dep / 'LocalFieldAudit', ('**/*.lean',))
    paths |= _files(dep / 'tools', ('*.lean', '*.py', '*.json'))
    paths |= _files(dep / '.vscode', ('*.json',))
    hashes = {p.resolve().as_posix(): digest(p) for p in paths if p.is_file()}
    identity = external_git_identity(dep / 'external-lock.json')
    hashes['external-git-identity.json'] = hashlib.sha256(
        json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return dict(sorted(hashes.items()))


def runtime_snapshot(imports: list[dict], prefix: str | Path,
                     extra_executables: Iterable[str | Path] = ()) -> dict[str, str]:
    """Hash every imported OLean and present sidecar, plus active tool binaries."""
    prefix = Path(prefix)
    paths = {prefix / 'bin' / name for name in ('lean.exe', 'lake.exe')}
    paths.update(Path(p) for p in extra_executables)
    for row in imports:
        base = Path(row['path'])
        paths.add(base)
        # Include present OLean metadata sidecars. Newly appearing files are found
        # on the second closure scan, even if they were absent in the first scan.
        for suffix in ('.private', '.server', '.hash'):
            sidecar = Path(str(base) + suffix)
            if sidecar.exists():
                paths.add(sidecar)
    missing = sorted(str(p) for p in paths if not p.is_file())
    if missing:
        raise RuntimeError('Missing runtime artifact(s): ' + ', '.join(missing))
    return {str(p.resolve()): digest(p) for p in sorted(paths, key=lambda x: str(x))}


def runtime_hash(runtime: dict[str, str]) -> str:
    return hashlib.sha256(json.dumps(runtime, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def save(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def run(args: list[str], label: str, timeout: int = 1800) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, encoding='utf-8',
                            errors='strict', capture_output=True, timeout=timeout)
    save(OUT / f'{label}.json', {'command': args, 'exit_code': result.returncode,
                                 'stdout': result.stdout, 'stderr': result.stderr})
    if result.returncode or result.stderr:
        raise RuntimeError(f'{label} failed or produced stderr: {result.stdout}\n{result.stderr}')
    return result.stdout


def one_information(output: str):
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
    by_id = {row['id']: row for row in binder_rows}
    declared = {}
    for item in catalog:
        name = item['id']
        if name not in by_id:
            raise RuntimeError(f'Binder audit missing catalog target: {name}')
        actual = sorted(b['name'] for b in by_id[name]['binders']
                        if b['isProp'] and b['isExplicit'] and not b['isInstance'])
        expected = sorted(item['hypotheses'])
        if actual != expected:
            raise RuntimeError(f'Undeclared or stale hypotheses for {name}: '
                               f'kernel reports {actual}, catalog declares {expected}')
        declared[name] = expected
    return declared


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


def receipt_valid(receipt, inputs, dependencies, runtime, catalog):
    evidence_name = receipt.get('evidence', '')
    if not isinstance(evidence_name, str) or not re.fullmatch(
            r'verification/vscode-observation-round[1-9][0-9]*\.txt',
            evidence_name):
        return False
    evidence = ROOT / evidence_name
    if not evidence.is_file():
        return False
    if not (receipt.get('schema') == 3 and receipt.get('input_sha256') == inputs
            and receipt.get('dependency_sha256') == dependencies
            and receipt.get('runtime_sha256') == runtime
            and receipt.get('evidence_sha256') == digest(evidence)
            and receipt.get('checked_targets') == sorted(x['id'] for x in catalog)
            and receipt.get('information_messages') == 2 * len(catalog)):
        return False
    file_rows = receipt.get('files', {})
    needed = {x['source'] for x in catalog} | {'tools/EditorCheck.lean'}
    for path in needed:
        row = file_rows.get(path, {})
        if (row.get('sha256') != inputs.get(path)
                or row.get('lean_server_checked') is not True
                or row.get('errors') != 0 or row.get('warnings') != 0):
            return False
        if path == 'tools/EditorCheck.lean' and row.get('information_messages') != 2 * len(catalog):
            return False
    return True


def check_editor_source(catalog):
    source = (ROOT / 'tools/EditorCheck.lean').read_text(encoding='utf-8')
    expected = sorted(x['id'] for x in catalog)
    for command in ('check', 'print axioms'):
        actual = sorted(re.findall(r'^#' + command + r'\s+(\S+)\s*$', source, re.M))
        if actual != expected:
            raise RuntimeError('Editor entry does not check every catalog target exactly once')


def main():
    OUT.mkdir(exist_ok=True)
    TREE.mkdir(exist_ok=True)
    save(TREE / 'facts.json', {'status': 'verification_in_progress', 'nodes': [], 'edges': []})
    (TREE / 'graph.dot').write_text('digraph facts {}\n', encoding='utf-8')
    (TREE / 'index.md').write_text('# bridge fact-tree\n\nVerification in progress.\n',
                                    encoding='utf-8')
    inputs_before = project_snapshot()
    deps_before = dependency_snapshot()
    catalog = json.loads((ROOT / 'tools/catalog.json').read_text(encoding='utf-8'))
    check_editor_source(catalog)
    expected_names = sorted(x['id'] for x in catalog)

    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('lake is not on PATH')
    version = run([lake, 'env', 'lean', '--version'], 'version').strip()
    if 'version 4.34.0-rc2' not in version:
        raise RuntimeError(f'Unexpected toolchain: {version}')
    prefix = Path(run([lake, 'env', 'lean', '--print-prefix'], 'prefix').strip())
    build = run([lake, '--no-cache', '--wfail', 'build', 'IUTBridge'], 'build')
    if 'warning:' in build.lower() or 'error:' in build.lower():
        raise RuntimeError('Build contains warning/error')

    imports = one_information(run([lake, 'env', 'lean', '--json',
        '-DwarningAsError=true', 'tools/ImportsRuntime.lean'], 'imports'))
    runtime_before = runtime_snapshot(imports, prefix)
    runtime_manifest = {'imports': imports, 'prefix': str(prefix),
                        'runtime_sha256': runtime_before,
                        'runtime_manifest_sha256': runtime_hash(runtime_before)}
    save(OUT / 'runtime-closure.json', runtime_manifest)

    for path in sorted(p for p in inputs_before
                       if p == 'IUTBridge.lean'
                       or (p.startswith('IUTBridge/') and p.endswith('.lean'))):
        output = run([lake, 'env', 'lean', '--json', '-DwarningAsError=true', path],
                     'source-' + path.replace('/', '-').removesuffix('.lean'))
        if output.strip():
            raise RuntimeError(f'Nonempty source diagnostics: {path}')

    rows = one_information(run([lake, 'env', 'lean', '--json',
        '-DwarningAsError=true', 'tools/Export.lean'], 'export'))
    by_id = {row['id']: row for row in rows}
    if len(by_id) != len(rows):
        raise RuntimeError('Duplicate exported constant')
    validate_catalog(catalog, by_id)
    binder_rows = one_information(run([lake, 'env', 'lean', '--json',
        '-DwarningAsError=true', 'tools/Binders.lean'], 'binders'))
    declared = audit_hypotheses(catalog, binder_rows)
    targets = {item['id'] for item in catalog}
    deps = {name: dependencies_via_helpers(name, by_id, targets) for name in targets}

    editor = run([lake, 'env', 'lean', '--json', '-DwarningAsError=true',
                  'tools/EditorCheck.lean'], 'editor-cli')
    messages = [json.loads(line) for line in editor.splitlines() if line.strip()]
    if len(messages) != 2 * len(catalog) or any(m['severity'] != 'information' for m in messages):
        raise RuntimeError('Unexpected editor-entry CLI diagnostics')
    for item in catalog:
        if set(by_id[item['id']]['axioms']) - ALLOWED_AXIOMS:
            raise RuntimeError(f'Unapproved axioms: {item["id"]}')

    # Re-export the import closure after all checking. This discovers modules or
    # sidecars that appeared during verification, instead of hashing only the
    # original list. Inputs, dependency identities, and runtime must all match.
    imports_after = one_information(run([lake, 'env', 'lean', '--json',
        '-DwarningAsError=true', 'tools/ImportsRuntime.lean'], 'imports-post'))
    runtime_after = runtime_snapshot(imports_after, prefix)
    if imports != imports_after or runtime_before != runtime_after:
        raise RuntimeError('Runtime import closure/artifacts changed during verification')
    if inputs_before != project_snapshot():
        raise RuntimeError('Project inputs changed during/after checking')
    if deps_before != dependency_snapshot():
        raise RuntimeError('Local-field dependency or external identity changed during checking')

    receipt_path = OUT / 'vscode-receipt.json'
    receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {}
    receipt_ok = receipt_valid(receipt, inputs_before, deps_before, runtime_before, catalog)
    eligible = set()
    if receipt_ok:
        for item in catalog:
            eligible.add(item['id'])
    admitted_ids = admission_closure(eligible, deps)
    nodes = []
    for item in sorted(catalog, key=lambda x: x['id']):
        name, path = item['id'], item['source']
        nodes.append({**by_id[name], 'source': path, 'sha256': inputs_before[path],
                      'hypotheses': declared[name], 'depends_on': sorted(deps[name]),
                      'scope': 'base-field Q_p bridge statements with declared hypotheses',
                      'status': 'admitted' if name in admitted_ids else 'awaiting_editor'})
    common = {'schema': 3, 'generated_utc': datetime.now(timezone.utc).isoformat(),
              'lean': version, 'input_sha256': inputs_before,
              'dependency_sha256': deps_before, 'runtime_sha256': runtime_before,
              'runtime_manifest_sha256': runtime_hash(runtime_before),
              'trust': 'Installed Lean kernel/runtime and standard axioms; editor receipt is an observation, not an anti-forgery attestation.',
              'scope': 'Catalog theorem DAG through project helper constants; external libraries are metadata, not fact-tree nodes.',
              'hypotheses_audited': True, 'iut_cor312_proved': False,
              'abc_proved': False, 'iut_object_constructed': False}
    save(OUT / 'checked-inputs.json', {**common, 'checked_targets': expected_names,
         'sources': sorted({x['source'] for x in catalog}),
         'receipt_valid': receipt_ok})
    save(OUT / 'project-constants.json', rows)
    save(OUT / 'binder-audit.json', {'generated_utc': common['generated_utc'],
         'declared_hypotheses': declared, 'rows': binder_rows})
    save(OUT / 'candidates.json', {**common, 'nodes': nodes})
    accepted = [row for row in nodes if row['status'] == 'admitted']
    edges = [{'from': dep, 'to': row['id']} for row in accepted for dep in row['depends_on']]
    save(TREE / 'facts.json', {**common, 'status': ('checked' if len(accepted) == len(nodes)
         else 'cli_verified_awaiting_editor'), 'nodes': accepted,
         'edges': edges, 'pending_count': len(nodes) - len(accepted)})
    lines = ['digraph facts {', '  rankdir=LR;']
    lines += [f'  "{row["id"]}";' for row in accepted]
    lines += [f'  "{edge["from"]}" -> "{edge["to"]}";' for edge in edges]
    (TREE / 'graph.dot').write_text('\n'.join(lines + ['}', '']), encoding='utf-8')
    index = ['# integrated bridge fact-tree', '',
             f'已准入 {len(accepted)} 个定理；待验收 {len(nodes) - len(accepted)} 个。', '',
             '所有节点均经过 source audit、定理依赖 DAG 与显式命题前提核验。', '',
             '| 定理 | 源文件 | 显式前提 | 目录定理依赖 |', '|---|---|---|---|']
    index += [f'| `{r["id"]}` | `{r["source"]}` | {", ".join(r["hypotheses"]) or "无"} | '
              f'{", ".join(r["depends_on"]) or "无"} |' for r in accepted]
    (TREE / 'index.md').write_text('\n'.join(index) + '\n', encoding='utf-8')
    print(f'Integrated CLI checks passed; admitted={len(accepted)}, '
          f'pending={len(nodes) - len(accepted)}, receipt_valid={receipt_ok}.')


if __name__ == '__main__':
    main()
