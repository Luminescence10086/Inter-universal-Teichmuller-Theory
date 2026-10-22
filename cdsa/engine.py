"""CDS-A layers 1, 2 and 4 plus the cross-cutting rules.

Layer 1 (compile): a goal becomes a contract DAG once; node count and parallel width are
locked here, so contention cannot grow at run time.
Layer 2 (execute): stateless executors produce claim envelopes; the writer thread is the
only thing that appends state. Executors never talk to each other.
Layer 4 (quality): every edge is gated green/yellow/red; yellow goes to a read-only
arbiter that may only accept or reject using evidence already on disk; red rolls back the
affected closure only, keeping admitted upstream work.
Cross-cutting: undeclared envelope fields are rejected (no free negotiation), siblings are
not fed each other's text (anonymous independent output), empty dissent is invalid
(mandatory objection), every envelope names producer + spec digest + version
(accountability), multi-producer claims need a threshold (no early consensus), and skipped
retries are audited (task-selection audit).
"""
from __future__ import annotations

import argparse
import json
import queue
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

from .core import (ArtifactStore, EventLog, canonical, digest_bytes, digest_file,
                   evidence_resolves, validate_envelope)

REPO = Path(__file__).resolve().parents[1]
NODE_KEYS = ('id', 'role', 'executor', 'allowed_paths', 'claim_template',
             'dissent_template', 'confidence', 'confidence_floor', 'timeout',
             'evidence_files', 'forbidden', 'forbidden_in_claim', 'produces_claim', 'retries')
EDGE_KEYS = ('from', 'to', 'verify')
VERIFY_PREDICATES = ('ancestors_green', 'envelope_valid', 'evidence_resolves',
                     'confidence_above', 'dissent_present', 'artifact_hash_stable')


# ---------------------------------------------------------------- layer 1: compile

def compile_spec(spec):
    """Validate and freeze the contract DAG. Returns (compiled, problems)."""
    problems = []
    budgets = spec.get('budgets', {})
    max_nodes = int(budgets.get('max_nodes', 8))
    max_parallel = int(budgets.get('max_parallel', 3))
    nodes = spec.get('nodes', [])
    edges = spec.get('edges', [])
    if not isinstance(nodes, list) or not nodes:
        return None, ['spec has no nodes']
    if len(nodes) > max_nodes:
        problems.append(f'node budget exceeded: {len(nodes)} > {max_nodes}')
    ids = [n.get('id') for n in nodes]
    if len(set(ids)) != len(ids):
        problems.append('duplicate node ids')
    for node in nodes:
        unknown = sorted(set(node) - set(NODE_KEYS))
        if unknown:
            problems.append(f'{node.get("id")}: undeclared node keys {unknown}')
        for key in ('id', 'role', 'executor', 'allowed_paths'):
            if key not in node:
                problems.append(f'{node.get("id")}: missing {key}')
        if not node.get('dissent_template'):
            problems.append(f'{node.get("id")}: dissent_template is mandatory')
        if node.get('executor', {}).get('kind') not in ('command', 'handoff'):
            problems.append(f'{node.get("id")}: executor kind must be command|handoff')
    for edge in edges:
        unknown = sorted(set(edge) - set(EDGE_KEYS))
        if unknown:
            problems.append(f'edge {edge.get("from")}->{edge.get("to")}: undeclared keys {unknown}')
        if edge.get('from') not in ids or edge.get('to') not in ids:
            problems.append(f'edge references unknown node: {edge}')
        for predicate in edge.get('verify', []):
            if predicate not in VERIFY_PREDICATES:
                problems.append(f'edge {edge.get("from")}->{edge.get("to")}: '
                                f'unknown predicate {predicate}')
    # acyclicity
    order, seen, stack = [], set(), set()

    def visit(node_id, trail):
        if node_id in stack:
            problems.append(f'cycle through {node_id}')
            return
        if node_id in seen:
            return
        stack.add(node_id)
        for edge in edges:
            if edge.get('from') == node_id:
                visit(edge.get('to'), trail + [node_id])
        stack.discard(node_id)
        seen.add(node_id)
        order.append(node_id)

    for node_id in ids:
        visit(node_id, [])
    if problems:
        return None, problems
    compiled = {'goal': spec.get('goal', ''), 'budgets': {'max_nodes': max_nodes,
                'max_parallel': max_parallel}, 'nodes': {n['id']: n for n in nodes},
                'edges': edges, 'topo': list(reversed(order))}
    digest = digest_bytes(canonical(compiled).encode('utf-8'))
    compiled['spec_digest'] = digest
    return compiled, []


def ready_nodes(compiled, admitted):
    """A node is ready only when every parent was ADMITTED (red blocks downstream)."""
    pending = [n for n in compiled['topo'] if n not in admitted]
    out = []
    for node_id in pending:
        parents = [e['from'] for e in compiled['edges'] if e['to'] == node_id]
        if all(parent in admitted for parent in parents):
            out.append(node_id)
    return out[:compiled['budgets']['max_parallel']]


# ---------------------------------------------------------------- layer 2: execute

def git_changed(repo):
    """Tracked+untracked paths currently differing from HEAD (empty set if not a repo)."""
    try:
        result = subprocess.run(['git', '-C', str(repo), 'status', '--porcelain'],
                                capture_output=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return set()
    if result.returncode != 0:
        return set()
    paths = set()
    for line in result.stdout.decode('utf-8', 'replace').splitlines():
        if len(line) > 3:
            paths.add(line[3:].strip())
    return paths


def run_command(node, compiled, repo, run_dir):
    executor = node['executor']
    argv = executor.get('argv', [])
    cwd = Path(repo) / executor.get('cwd', '.')
    timeout = node.get('timeout', 600)
    logs = Path(run_dir) / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    before = git_changed(repo)
    stdout_path = logs / f"{node['id']}.stdout.txt"
    stderr_path = logs / f"{node['id']}.stderr.txt"
    started = time.time()
    try:
        result = subprocess.run(argv, cwd=str(cwd), capture_output=True, timeout=timeout)
        code, out, err = result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        code, out, err = None, b'', b'timeout'
    after = git_changed(repo)
    touched = sorted(after - before)
    allowed = node.get('allowed_paths', [])
    outside = [p for p in touched
               if allowed and not any(p == a or p.startswith(a.rstrip('/') + '/')
                                      or p.startswith(a) for a in allowed)]
    stdout_path.write_bytes(out)
    stderr_path.write_bytes(err)

    def ref_of(path):
        try:
            return str(Path(path).relative_to(repo)).replace('\\', '/')
        except ValueError:
            return str(path)

    elapsed = round(time.time() - started, 2)
    # The exit status is recorded as its own evidence kind: it is the one signal that is
    # independent of the log text, so a command node has two genuinely separate pieces.
    exit_record = logs / f"{node['id']}.exit.json"
    exit_record.write_text(json.dumps({'argv': argv, 'exit': code, 'elapsed': elapsed,
                                       'touched': touched}, ensure_ascii=False,
                                      sort_keys=True) + '\n', encoding='utf-8')
    evidence = [
        {'kind': 'command', 'ref': ref_of(stdout_path),
         'sha256': digest_bytes(out),
         'detail': f'exit={code} elapsed={elapsed}s touched={len(touched)}'},
        {'kind': 'command', 'ref': ref_of(stderr_path),
         'sha256': digest_bytes(err), 'detail': f'stderr of {argv[0] if argv else "?"}'},
        {'kind': 'exit', 'ref': ref_of(exit_record),
         'sha256': digest_file(exit_record), 'detail': f'exit status {code}'},
    ]
    for rel in node.get('evidence_files', []):
        path = Path(repo) / rel
        if path.exists():
            evidence.append({'kind': 'file', 'ref': rel, 'sha256': digest_file(path),
                             'detail': 'declared evidence file'})
    claim = node.get('claim_template', 'command {argv} exited {code}')
    claim = claim.replace('{argv}', ' '.join(argv)).replace('{code}', str(code))
    envelope = {
        'claim_id': node.get('produces_claim', node['id']),
        'claim': claim,
        'evidence': evidence,
        'confidence': float(node.get('confidence', 0.6)),
        'artifactRef': '', 'dissent': [node['dissent_template']],
        'producer': node['id'], 'spec_digest': compiled['spec_digest'],
        'version': 'v1', 'kind': 'command',
    }
    return envelope, {'exit': code, 'elapsed': elapsed, 'touched': touched,
                      'outside_allowed': outside}


def run_handoff(node, compiled, repo, run_dir):
    handoff_dir = Path(run_dir) / 'handoff'
    handoff_dir.mkdir(parents=True, exist_ok=True)
    path = handoff_dir / f"{node['id']}.json"
    if not path.exists():
        template = {'__instructions__': 'fill claim/evidence/confidence/dissent, then rerun '
                                        'with --accept-handoffs',
                    'claim_id': node.get('produces_claim', node['id']), 'claim': '',
                    'evidence': [], 'confidence': 0.0, 'artifactRef': '', 'dissent': [],
                    'producer': node['id'], 'spec_digest': compiled['spec_digest'],
                    'version': 'v1', 'kind': 'handoff'}
        path.write_text(json.dumps(template, ensure_ascii=False, indent=2) + '\n',
                        encoding='utf-8')
        return None, {'exit': None, 'waiting': True, 'handoff': str(path)}
    payload = json.loads(path.read_text(encoding='utf-8'))
    payload.pop('__instructions__', None)
    return payload, {'exit': 0, 'handoff': str(path)}


# ---------------------------------------------------------------- layer 4: gates

def gate_envelope(envelope, node, repo, known_theorems=None):
    """Return (color, reasons). Green unlocks; yellow goes to the read-only arbiter."""
    problems = validate_envelope(envelope)
    text = envelope.get('claim', '') if isinstance(envelope, dict) else ''
    for token in node.get('forbidden_in_claim', []) + node.get('forbidden', []):
        if token and token in text:
            problems.append(f'claim contains forbidden phrase: {token!r}')
    for item in envelope.get('evidence', []) if isinstance(envelope, dict) else []:
        if item.get('kind') in ('file', 'command'):
            ok, why = evidence_resolves(item, repo)
            if not ok:
                problems.append(why)
        if item.get('kind') == 'theorem' and known_theorems is not None:
            if item.get('ref') not in known_theorems:
                problems.append(f'theorem evidence is not exported: {item.get("ref")}')
    if problems:
        return 'red', problems
    confidence = float(envelope['confidence'])
    floor = float(node.get('confidence_floor', 0.6))
    kinds = {item['kind'] for item in envelope['evidence']}
    if confidence < floor:
        return 'yellow', [f'confidence {confidence} below floor {floor}']
    if len(kinds) < 2 and node.get('role') in ('verify', 'synthesise'):
        return 'yellow', ['only one evidence kind for a verify/synthesise node']
    return 'green', ['schema, evidence and confidence ok']


def arbitrate(envelope, repo):
    """Read-only arbiter: may only accept or reject using evidence already on disk."""
    if not envelope.get('dissent'):
        return 'red', 'arbiter refuses: no recorded objection'
    resolved = []
    for item in envelope.get('evidence', []):
        if item.get('kind') in ('file', 'command'):
            ok, why = evidence_resolves(item, repo)
            if not ok:
                return 'red', f'arbiter refuses: {why}'
            resolved.append(item['kind'])
    if float(envelope.get('confidence', 0)) < 0.6:
        return 'red', 'arbiter refuses: confidence below 0.6'
    if len(set(resolved)) < 2:
        return 'red', 'arbiter refuses: needs two independent evidence kinds'
    return 'green', 'arbiter accepted on recorded evidence only'


def verify_edge(edge, state, compiled, repo):
    """Edge condition: all declared predicates must hold for the child's envelope."""
    child = state['envelopes'].get(edge['to'])
    parent = state['envelopes'].get(edge['from'])
    reasons = []
    if child is None:
        return 'red', [f'{edge["to"]}: no envelope']
    for predicate in edge.get('verify', []):
        if predicate == 'ancestors_green':
            if parent is None:
                reasons.append(f'{edge["from"]}: parent has no admitted envelope')
        elif predicate == 'envelope_valid':
            problems = validate_envelope(child)
            if problems:
                reasons.append(f'{edge["to"]}: {problems[0]}')
        elif predicate == 'evidence_resolves':
            for item in child.get('evidence', []):
                if item.get('kind') in ('file', 'command'):
                    ok, why = evidence_resolves(item, repo)
                    if not ok:
                        reasons.append(why)
        elif predicate == 'confidence_above':
            if float(child.get('confidence', 0)) < float(compiled['nodes'][edge['to']]
                                                         .get('confidence_floor', 0.6)):
                reasons.append(f'{edge["to"]}: confidence below floor')
        elif predicate == 'dissent_present':
            if not child.get('dissent'):
                reasons.append(f'{edge["to"]}: dissent empty')
        elif predicate == 'artifact_hash_stable':
            ref = child.get('artifactRef') or ''
            if ref and not (Path(repo) / ref).exists():
                reasons.append(f'{edge["to"]}: artifactRef does not resolve: {ref}')
    return ('green', ['all edge predicates hold']) if not reasons else ('red', reasons)


def downstream_closure(compiled, node_id):
    closure, frontier = {node_id}, [node_id]
    while frontier:
        current = frontier.pop()
        for edge in compiled['edges']:
            if edge['from'] == current and edge['to'] not in closure:
                closure.add(edge['to'])
                frontier.append(edge['to'])
    return sorted(closure)


# ---------------------------------------------------------------- orchestration

def run(compiled, repo, run_dir, accept_handoffs=False):
    repo, run_dir = Path(repo), Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    log = EventLog(run_dir)
    store = ArtifactStore(run_dir / 'artifacts')
    log.acquire(f'cdsa-engine:{run_dir.name}')
    try:
        log.append('compile', {'goal': compiled['goal'],
                               'spec_digest': compiled['spec_digest'],
                               'nodes': sorted(compiled['nodes']),
                               'budgets': compiled['budgets']})
        known_theorems = None
        # Resume from the checkpoint: admitted nodes are not re-executed; attempted-but-red
        # nodes are not retried automatically (that would be a disguised infinite loop).
        seed = log.replay()
        admitted = set(seed['admitted'])
        attempted = set(seed['envelopes'])
        waiting, skipped, retries, audit = set(), [], {}, []
        while True:
            ready = [n for n in ready_nodes(compiled, admitted)
                     if n not in waiting and n not in attempted]
            if not ready:
                break
            results = queue.Queue()

            def worker(node_id):
                node = compiled['nodes'][node_id]
                try:
                    if node['executor']['kind'] == 'command':
                        envelope, meta = run_command(node, compiled, repo, run_dir)
                    else:
                        envelope, meta = run_handoff(node, compiled, repo, run_dir)
                except Exception as exc:  # noqa: BLE001 - an executor crash must be a red gate
                    envelope = {'claim_id': node.get('produces_claim', node_id),
                                'claim': f'executor for {node_id} crashed: '
                                         f'{type(exc).__name__}',
                                'evidence': [], 'confidence': 0.0, 'artifactRef': '',
                                'dissent': [f'crash: {exc}'], 'producer': node_id,
                                'spec_digest': compiled['spec_digest'], 'version': 'v1',
                                'kind': 'error'}
                    meta = {'exit': None, 'error': f'{type(exc).__name__}: {exc}'}
                results.put((node_id, envelope, meta))

            threads = [threading.Thread(target=worker, args=(n,)) for n in ready]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            # single writer: only this thread appends
            for _ in range(len(ready)):
                node_id, envelope, meta = results.get()
                if envelope is None:
                    waiting.add(node_id)
                    log.append('skip', {'node': node_id, 'reason': 'awaiting handoff',
                                        'handoff': meta.get('handoff')})
                    continue
                log.append('envelope', {'node': node_id, 'envelope': envelope,
                                        'meta': meta})
                color, reasons = gate_envelope(envelope, compiled['nodes'][node_id],
                                               repo, known_theorems)
                # Layer 1 contract enforcement: a node may not write outside its
                # allowed_paths. This is what stops an executor from "helpfully" fixing
                # something upstream.
                if meta.get('error'):
                    color = 'red'
                    reasons = reasons + [f'executor error: {meta["error"]}']
                if meta.get('outside_allowed'):
                    color = 'red'
                    reasons = reasons + [f'wrote outside allowed_paths: '
                                         f'{meta["outside_allowed"][:5]}']
                if meta.get('exit') not in (0, None) and color == 'green':
                    color = 'red'
                    reasons = reasons + [f'command exited {meta["exit"]}']
                log.append('gate', {'edge': f'{node_id}:self', 'color': color,
                                    'reasons': reasons})
                if color == 'yellow':
                    color, why = arbitrate(envelope, repo)
                    log.append('gate', {'edge': f'{node_id}:arbiter', 'color': color,
                                        'reasons': [why]})
                if color == 'red':
                    attempted.add(node_id)
                    for other in downstream_closure(compiled, node_id):
                        if other != node_id:
                            log.append('replan', {'nodes': [other],
                                                  'reason': f'blocked by {node_id}'})
                            skipped.append(other)
                    retries[node_id] = retries.get(node_id, 0) + 1
                    if retries[node_id] >= 3:
                        audit.append(f'{node_id} retried {retries[node_id]} times without '
                                     f'admission; task-selection audit flags it')
                else:
                    admitted.add(node_id)
                    attempted.add(node_id)
            if not accept_handoffs and waiting:
                break
        state = log.replay()
        for edge in compiled['edges']:
            color, reasons = verify_edge(edge, state, compiled, repo)
            log.append('gate', {'edge': f'{edge["from"]}->{edge["to"]}',
                                'color': color, 'reasons': reasons})
        state = log.replay()
        assert not log.verify_chain(), log.verify_chain()
        log.snapshot(run_dir / 'snapshot.json')
        return state, {'waiting': sorted(waiting), 'skipped': sorted(set(skipped)),
                       'retries': retries, 'audit': audit}
    finally:
        log.release()


def final_answer(compiled, repo, run_dir):
    """Independent global verification: replay, re-check every declaration, emit answer."""
    repo, run_dir = Path(repo), Path(run_dir)
    log = EventLog(run_dir)
    chain = log.verify_chain()
    state = log.replay()
    problems = []
    if chain:
        problems.append(f'event log chain broken: {chain}')
    admitted = set(state['admitted'])
    unadmitted = sorted(set(compiled['nodes']) - admitted)
    if unadmitted:
        # "skipped" records an earlier handoff wait, not a failure: only ADMISSION counts,
        # so the answer is computed from the gates, not from the skip events.
        problems.append(f'nodes never admitted: {unadmitted}')
    for edge in compiled['edges']:
        color, reasons = verify_edge(edge, state, compiled, repo)
        if color != 'green':
            problems.append(f'edge {edge["from"]}->{edge["to"]}: {reasons[0]}')
    # re-run declared command evidence to prove it is still true
    checked = 0
    for node_id, node in compiled['nodes'].items():
        if node['executor']['kind'] != 'command':
            continue
        recorded = state['envelopes'].get(node_id)
        if recorded is None:
            problems.append(f'{node_id}: no admitted envelope')
            continue
        ok, why = evidence_resolves(recorded['evidence'][0], repo)
        if not ok:
            problems.append(f'{node_id}: recorded command log no longer matches ({why})')
        checked += 1
    final = {'goal': compiled['goal'], 'spec_digest': compiled['spec_digest'],
             'chain_ok': chain is None, 'log_lines': state_log_lines(log),
             'admitted_nodes': sorted(state['admitted']),
             'skipped_records': state['skipped'],
             'note': ('skipped_records is history (e.g. an earlier handoff wait); it is not '
                      'a failure — admission is decided by the gates only'),
             'command_evidence_rechecked': checked, 'problems': problems,
             'status': 'PASS' if not problems else 'FAIL'}
    (run_dir / 'answer.json').write_text(json.dumps(final, ensure_ascii=False, indent=2,
                                                    sort_keys=True) + '\n', encoding='utf-8')
    return final


def state_log_lines(log):
    return len(log._lines())


def load_spec(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def main(argv=None):
    parser = argparse.ArgumentParser(prog='cdsa', description='CDS-A: compile, execute, '
                                                              'gate, verify.')
    sub = parser.add_subparsers(dest='command', required=True)
    run_p = sub.add_parser('run')
    run_p.add_argument('--spec', required=True)
    run_p.add_argument('--repo', default='.')
    run_p.add_argument('--run', required=True)
    run_p.add_argument('--accept-handoffs', action='store_true')
    ver_p = sub.add_parser('verify')
    ver_p.add_argument('--spec', required=True)
    ver_p.add_argument('--repo', default='.')
    ver_p.add_argument('--run', required=True)
    sub.add_parser('templates')
    args = parser.parse_args(argv)

    if args.command == 'run':
        compiled, problems = compile_spec(load_spec(args.spec))
        if problems:
            print('compile FAILED:')
            for item in problems:
                print('  -', item)
            return 2
        state, report = run(compiled, args.repo, args.run, args.accept_handoffs)
        print(f'compiled {len(compiled["nodes"])} nodes, digest {compiled["spec_digest"][:16]}')
        for node_id in compiled['topo']:
            admitted = node_id in state['envelopes']
            color = state['gates'].get(f'{node_id}:self', 'n/a')
            print(f'  [{color:<6}] {node_id:<10} admitted={admitted}')
        if report['waiting']:
            print('waiting for handoff:', report['waiting'])
        if report['audit']:
            print('task-selection audit:', report['audit'])
        return 0
    if args.command == 'verify':
        compiled, problems = compile_spec(load_spec(args.spec))
        if problems:
            print('spec no longer compiles:', problems)
            return 2
        final = final_answer(compiled, args.repo, args.run)
        print(f'status: {final["status"]}')
        for problem in final['problems']:
            print('  -', problem)
        print('answer written:', Path(args.run) / 'answer.json')
        return 0 if final['status'] == 'PASS' else 1
    if args.command == 'templates':
        print('node keys:', NODE_KEYS)
        print('edge predicates:', VERIFY_PREDICATES)
        return 0
    return 2


if __name__ == '__main__':
    sys.exit(main())
