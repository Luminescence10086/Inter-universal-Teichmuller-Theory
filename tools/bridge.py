"""Cross-project bridge auditor.

The repository now has three verification projects on two Lean toolchains:

    main       Lean 4.34.0      (no Mathlib)   abstract discrete models
    local      Lean 4.34.0-rc2  (Mathlib)      audited real Q_p filtration
    bridge     Lean 4.34.0-rc2  (Mathlib)      base-field realization + contracts

`bridge` imports `local`, so that edge is a kernel-checked dependency. No proof
can be imported from `main` into `bridge` (different toolchain), so every
main-to-bridge edge is an *audited contract* instead: the elaborated statements
are compared as text after namespace normalisation, and vendored definitions are
compared by their elaborated types AND diagnostic definition-body text. This tool performs that audit and
refuses to describe it as a proof transfer.

What it does NOT do: it does not prove the bridge. Text comparisons are conservative
change/correspondence checks, not a proof of semantic equivalence. Every
result records `proof_transfer: false`.

Exit code is non-zero on any inconsistency, including a stale export.
"""
from __future__ import annotations
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from freshness import validate_project
from semantic_lock import definition_bodies

ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = ROOT / 'bridges' / 'contracts.json'
OUT = ROOT / 'bridges'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
PROJECTS = {'main': ROOT, 'local': ROOT / 'local-field', 'bridge': ROOT / 'bridge'}
# Honest labels for how strong a given edge is.
STRENGTH = {'kernel_checked_import': 'import', 'contract': 'contract'}


def load_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def norm_statement(text, prefixes):
    for prefix in prefixes:
        text = text.replace(prefix, '')
    return re.sub(r'\s+', ' ', text).strip()


def vendored_matches(left, right, left_body, right_body, prefixes):
    """Two distinct textual checks; neither is cross-kernel proof transfer."""
    return (norm_statement(left['statement'], prefixes) ==
            norm_statement(right['statement'], prefixes),
            norm_statement(left_body, prefixes) == norm_statement(right_body, prefixes))


def project_constants(project):
    """Load a project's exported constants, refusing a stale export."""
    base = PROJECTS[project]
    const_path = base / 'verification' / 'project-constants.json'
    check_path = base / 'verification' / 'checked-inputs.json'
    if not const_path.exists():
        raise RuntimeError(f'{project}: missing verification/project-constants.json; '
                           f'run the project verifier first')
    if not check_path.exists():
        raise RuntimeError(f'{project}: missing verification/checked-inputs.json')
    # Recompute complete source/config/tool input sets, dependency identity and
    # actual imported runtime. Pending CLI candidates cannot certify contracts.
    return validate_project(base, deep=True)


def require_theorem(project, name, rows_by_id):
    if name not in rows_by_id:
        raise RuntimeError(f'{project}: theorem not exported: {name}')
    row = rows_by_id[name]
    if row['kind'] != 'theorem':
        raise RuntimeError(f'{project}: {name} is a {row["kind"]}, not a theorem')
    bad = set(row['axioms']) - ALLOWED_AXIOMS
    if bad:
        raise RuntimeError(f'{project}: {name} uses unapproved axioms {sorted(bad)}')
    return row


def main():
    spec = load_json(CONTRACTS)
    prefixes = spec['normalisation']['strip_prefixes']
    rows = {}
    for project in PROJECTS:
        rows[project], _ = project_constants(project)
    bodies = {project: definition_bodies(PROJECTS[project]) for project in ('main', 'bridge')}

    results = []
    failures = []
    for contract in spec['contracts']:
        cid = contract['id']
        checks = []
        abstract_row = None
        if contract.get('abstract'):
            a = contract['abstract']
            abstract_row = require_theorem(a['project'], a['theorem'], rows[a['project']])
            checks.append(f'abstract endpoint elaborated: {a["theorem"]}')

        concrete_rows = []
        for item in contract.get('concrete', []):
            row = require_theorem(item['project'], item['theorem'], rows[item['project']])
            concrete_rows.append((item, row))
        checks.append(f'{len(concrete_rows)} concrete endpoint(s) elaborated, axioms approved')

        if contract['kind'] == 'statement_identity':
            for item, row in concrete_rows:
                left = norm_statement(abstract_row['statement'], prefixes)
                right = norm_statement(row['statement'], prefixes)
                if left != right:
                    msg = (f'{cid}: statements differ\n  abstract: {left}\n  concrete: {right}')
                    failures.append(msg)
                else:
                    checks.append('elaborated statements identical after prefix normalisation')
        elif abstract_row is not None:
            # An instantiation is a weaker edge: record both shapes, enforce that the
            # contract states which IUT objects are *not* constructed.
            checks.append('instantiation edge: statements differ by design, no identity claimed')
            if not contract.get('not_constructed'):
                failures.append(f'{cid}: instantiation contract must list what is not constructed')

        for vendored in contract.get('vendored', []):
            left = rows['main'][vendored['main']]
            right = rows['bridge'][vendored['bridge']]
            lnorm = norm_statement(left['statement'], prefixes)
            rnorm = norm_statement(right['statement'], prefixes)
            type_match, body_match = vendored_matches(left, right,
                bodies['main'][vendored['main']], bodies['bridge'][vendored['bridge']], prefixes)
            if not type_match:
                failures.append(f'{cid}: vendored type mismatch for {vendored["main"]}: '
                                f'{lnorm} vs {rnorm}')
            else:
                checks.append(f'vendored definition type identical: {vendored["main"].split(".")[-1]}')
            lbody = norm_statement(bodies['main'][vendored['main']], prefixes)
            rbody = norm_statement(bodies['bridge'][vendored['bridge']], prefixes)
            if not body_match:
                failures.append(f'{cid}: vendored definition body mismatch: {vendored["main"]}')
            else:
                checks.append(f'vendored definition body text identical: {vendored["main"].split(".")[-1]}')

        if not contract.get('iut_objects_constructed'):
            checks.append('contract declares no IUT object constructed')
        else:
            failures.append(f'{cid}: contract claims an IUT object was constructed; this round '
                            f'constructed none, so the contract must not say otherwise')

        results.append({
            'id': cid,
            'kind': contract['kind'],
            'claim': contract['claim'],
            'abstract': contract.get('abstract'),
            'concrete': [item['theorem'] for item in contract.get('concrete', [])],
            'external_anchors': contract.get('external_anchors', []),
            'not_constructed': contract.get('not_constructed', []),
            'checks': checks,
            'proof_transfer': False,
            'edge_strength': 'contract',
            'status': 'checked' if not any(cid in f for f in failures) else 'failed',
        })

    # The local-to-bridge edge is a real import; record it as such.
    bridge_row = rows['bridge'].get('IUTBridge.ScaleLedger.mem_layer_iff_le_valuation')
    import_edge = None
    if bridge_row is not None:
        uses = [c for c in bridge_row['constants']
                if c.startswith('LocalFieldAudit.Filtration.')]
        import_edge = {
            'from': 'local',
            'to': 'bridge',
            'edge_strength': 'kernel_checked_import',
            'evidence': uses[:8],
            'note': 'bridge/IUTBridge/ScaleLedger.lean imports LocalFieldAudit.Filtration; '
                    'the dependency is checked by the Lean kernel, not by this auditor.',
        }

    summary = {
        'schema': 1,
        'generated_utc': datetime.now(timezone.utc).isoformat(),
        'projects': {p: str(PROJECTS[p].relative_to(ROOT)) or '.' for p in PROJECTS},
        'contracts': results,
        'import_edge': import_edge,
        'failures': failures,
        'status': 'all_contracts_checked' if not failures else 'contract_failures',
        'cross_toolchain_proof_transfer': False,
        'iut_object_constructed': False,
        'iut_cor312_proved': False,
        'abc_proved': False,
        'scope': ('Statement/structure correspondence between an abstract discrete model '
                  'and an audited base-field Q_p theory. Not an IUT result.'),
    }
    OUT.mkdir(exist_ok=True)
    (OUT / 'facts.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n',
                                    encoding='utf-8')

    lines = ['# Bridge contracts', '',
             f'生成时间：{summary["generated_utc"]}；状态：`{summary["status"]}`。', '',
             '三套工程、两套工具链。`local → bridge` 是**真实 Lean import**（内核检查）；',
             '`main → bridge` **无法 import**（Lean 4.34.0 vs rc2），因此那里的边是**受审计的接口合同**：',
             '完整检查准入、源/配置/依赖/运行产物，再比较陈述及指定定义体文本；**不是**证明转移。', '',
             '| 合同 | 类型 | 抽象端 | 具体端 | 结论 |', '|---|---|---|---|---|']
    for r in results:
        abstract = r['abstract']['theorem'] if r['abstract'] else '—（新结果）'
        lines.append(f'| `{r["id"]}` | {r["kind"]} | `{abstract}` | '
                     + '<br>'.join(f'`{c}`' for c in r['concrete'])
                     + f' | {r["status"]} |')
    lines += ['', '## 每条合同的机器检查项', '']
    for r in results:
        lines.append(f'### {r["id"]}')
        lines.append('')
        lines.append(r['claim'])
        lines.append('')
        for check in r['checks']:
            lines.append(f'- ✅ {check}')
        if r['not_constructed']:
            lines.append(f'- 未构造：{", ".join(r["not_constructed"])}')
        lines.append('')
    if failures:
        lines += ['## 失败项', ''] + [f'- ❌ {f}' for f in failures] + ['']
    (OUT / 'index.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')

    print(f'Contracts checked: {len(results)}; failures: {len(failures)}; '
          f'proof_transfer: false')
    for f in failures:
        print('  FAIL', f)
    return 0 if not failures else 1


if __name__ == '__main__':
    sys.exit(main())
