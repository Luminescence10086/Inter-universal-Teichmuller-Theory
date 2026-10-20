"""Query three checked projects on two toolchains; mark actual import edges."""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = [('core', ROOT), ('local-field', ROOT / 'local-field'), ('bridge', ROOT / 'bridge')]

def checked(query, deep):
    results = []
    for label, root in PROJECTS:
        script = 'query_integrated.py' if label == 'bridge' else 'query.py'
        args = [sys.executable, str(root / 'tools' / script), query]
        if deep:
            args.append('--deep')
        result = subprocess.run(args, cwd=root, text=True, encoding='utf-8',
            capture_output=True, timeout=300)
        if result.returncode or result.stderr:
            raise RuntimeError(f'{label} is not currently verified: {result.stdout}\n{result.stderr}')
        path = root / 'fact-tree/facts.json'
        data = json.loads(path.read_text(encoding='utf-8'))
        if data.get('pending_count') != 0:
            raise RuntimeError(f'{label} still has pending targets')
        results.append((label, root, data, result.stdout,
                        hashlib.sha256(path.read_bytes()).hexdigest()))
    return results

def refresh(deep):
    results = checked('__FOREST_VALIDATE_NO_THEOREM_MATCH__', deep)
    nodes, edges, projects, seen = [], [], [], set()
    for label, root, data, _, sha in results:
        for row in data['nodes']:
            if row['id'] in seen:
                raise RuntimeError('Duplicate theorem ID across projects')
            seen.add(row['id'])
            nodes.append({**row, 'project': label, 'lean': data['lean']})
        edges.extend(data['edges'])
        projects.append({'project': label, 'root': str(root), 'lean': data['lean'],
            'facts_sha256': sha, 'nodes': len(data['nodes']), 'edges': len(data['edges'])})
    # Follow bridge project helper constants to already admitted local-field
    # catalog theorems. Both projects use the same rc2 kernel and an actual import.
    # Core-to-bridge contracts are deliberately absent from this proof DAG.
    from freshness import verifier
    local_rows = json.loads((ROOT / 'local-field/verification/project-constants.json').read_text(encoding='utf-8'))
    bridge_rows = json.loads((ROOT / 'bridge/verification/project-constants.json').read_text(encoding='utf-8'))
    all_rows = {r['id']: r for r in local_rows + bridge_rows}
    local_ids = {r['id'] for r in nodes if r['project'] == 'local-field'}
    bridge_ids = {r['id'] for r in nodes if r['project'] == 'bridge'}
    gate = verifier(ROOT / 'bridge')
    cross = []
    for name in sorted(bridge_ids):
        for dep in sorted(gate.dependencies_via_helpers(name, all_rows, local_ids | bridge_ids) & local_ids):
            cross.append({'from': dep, 'to': name, 'kind': 'kernel_checked_import'})
    edges.extend(cross)
    registry = {'schema': 2, 'generated_utc': datetime.now(timezone.utc).isoformat(),
        'purpose': 'Convenience registry of separately checked theorem DAGs; no cross-toolchain proof import.',
        'projects': projects, 'nodes': nodes, 'edges': edges,
        'cross_project_import_edges': cross,
        'abc_proved': False, 'iut_cor312_proved': False}
    (ROOT / 'fact-tree/registry.json').write_text(json.dumps(registry, ensure_ascii=False,
        indent=2) + '\n', encoding='utf-8')
    graph = ['digraph checked_forest {', '  rankdir=LR;']
    for i, (label, _, data, _, _) in enumerate(results):
        graph += [f'  subgraph cluster_{i} {{', f'    label="{label}";']
        graph += [f'    "{r["id"]}";' for r in data['nodes']]
        graph += ['  }']
    graph += [f'  "{e["from"]}" -> "{e["to"]}";' for e in edges]
    (ROOT / 'fact-tree/combined.dot').write_text('\n'.join(graph + ['}', '']), encoding='utf-8')
    lines = ['# 已验收定理总入口', '',
        f'共 {len(nodes)} 个节点、{len(edges)} 条边；来自三个工程、两个工具链。', '',
        '目录是调用入口，不是跨工具链的 Lean import。没有证明真实 IUT 或 abc。', '',
        '| 工程 | 节点 | 边 | Lean | 逐项目录 |', '|---|---:|---:|---|---|']
    for p in projects:
        index = 'index.md' if p['project'] == 'core' else f'../{p["project"]}/fact-tree/index.md'
        lines.append(f'| {p["project"]} | {p["nodes"]} | {p["edges"]} | {p["lean"]} | [声明与依赖]({index}) |')
    lines += ['', '查询：`python tools/forest.py query 关键词`；深查：追加 `--deep`。',
        '重建本入口：`python tools/forest.py refresh --deep`。', '',
        '实际准入依据仍为各工程 facts.json。查询会重新检查源快照，深查会重算运行产物哈希。',
        f'其中 {len(cross)} 条跨工程边来自 local-field → bridge 的实际 import；接口合同不混入证明边。',
        'registry.json 和 combined.dot 是可重建快照；源代码变化后须重新验证并 refresh。', '']
    (ROOT / 'fact-tree/catalogue.md').write_text('\n'.join(lines), encoding='utf-8')
    print(f'Checked forest: {len(nodes)} nodes, {len(edges)} edges, {len(projects)} toolchains.')

def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['query', 'refresh'])
    parser.add_argument('query', nargs='?', default='')
    parser.add_argument('--deep', action='store_true')
    args = parser.parse_args()
    if args.action == 'refresh':
        refresh(args.deep)
    else:
        results = checked(args.query, args.deep)
        for label, _, _, output, _ in results:
            if output:
                print(f'[{label}]\n{output}', end='')

if __name__ == '__main__':
    main()
