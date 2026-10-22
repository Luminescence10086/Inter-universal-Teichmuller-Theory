"""CDS-A layer 3 (state) and layer 2's wire format (claim envelopes + artifact store).

Two ideas, both enforced rather than documented:

* **single writer, append-only, hash-chained.** Every state change is one JSON line in
  ``events.jsonl`` carrying ``seq``, ``prev`` (hash of the previous line) and ``hash``.
  A snapshot is a deterministic fold over the log, so any snapshot can be replayed and
  any tampering shows up as a broken chain. Only the process holding ``writer.lock``
  may append; read-only participants read snapshots.
* **envelopes carry claims, not conversations.** An envelope has a fixed field set
  (unknown fields are rejected), evidence entries must resolve to real bytes or a real
  command log, and ``dissent`` must be non-empty — "what could make this wrong" is a
  required field, not a courtesy.
"""
from __future__ import annotations

import hashlib
import json
import os
import time
from pathlib import Path

ENVELOPE_KEYS = ('claim_id', 'claim', 'evidence', 'confidence', 'artifactRef',
                 'dissent', 'producer', 'spec_digest', 'version', 'kind')
EVIDENCE_KEYS = ('kind', 'ref', 'sha256', 'detail')


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def canonical(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',', ':'))


class ArtifactStore:
    """Content-addressed blobs. Envelopes carry the hash, never the payload."""

    def __init__(self, root):
        self.root = Path(root)
        self.root.mkdir(parents=True, exist_ok=True)

    def put(self, data: bytes, label='blob') -> dict:
        sha = digest_bytes(data)
        path = self.root / sha
        if not path.exists():
            path.write_bytes(data)
        return {'sha256': sha, 'size': len(data), 'label': label,
                'path': str(path.relative_to(self.root.parent.parent))}

    def get(self, sha):
        path = self.root / sha
        if not path.exists():
            raise KeyError(f'artifact missing: {sha}')
        data = path.read_bytes()
        if digest_bytes(data) != sha:
            raise ValueError(f'artifact corrupted: {sha}')
        return data


class EventLog:
    """Append-only hash chain with a single-writer lock."""

    def __init__(self, run_dir):
        self.run_dir = Path(run_dir)
        self.run_dir.mkdir(parents=True, exist_ok=True)
        self.path = self.run_dir / 'events.jsonl'
        self.lock_path = self.run_dir / 'writer.lock'

    def _lines(self):
        if not self.path.exists():
            return []
        return [json.loads(line) for line in
                self.path.read_text(encoding='utf-8').splitlines() if line.strip()]

    def locked(self):
        return self.lock_path.exists()

    def acquire(self, owner):
        if self.lock_path.exists():
            held = json.loads(self.lock_path.read_text(encoding='utf-8'))
            raise RuntimeError(f"state is single-writer; held by {held.get('owner')!r}")
        self.lock_path.write_text(canonical({'owner': owner, 'pid': os.getpid(),
                                            'at': time.time()}), encoding='utf-8')

    def release(self):
        if self.lock_path.exists():
            self.lock_path.unlink()

    def append(self, event_type, payload):
        if not self.lock_path.exists():
            raise RuntimeError('refusing to append without the writer lock')
        lines = self._lines()
        prev = lines[-1]['hash'] if lines else 'genesis'
        body = {'seq': len(lines) + 1, 'type': event_type, 'payload': payload,
                'at': round(time.time(), 3), 'prev': prev}
        body['hash'] = digest_bytes(canonical(body).encode('utf-8'))
        with self.path.open('a', encoding='utf-8') as stream:
            stream.write(canonical(body) + '\n')
        return body

    def verify_chain(self):
        prev = 'genesis'
        for index, line in enumerate(self._lines(), start=1):
            body = {k: v for k, v in line.items() if k != 'hash'}
            if line.get('seq') != index:
                return f'seq gap at line {index}'
            if line.get('prev') != prev:
                return f'broken prev link at line {index}'
            if digest_bytes(canonical(body).encode('utf-8')) != line.get('hash'):
                return f'hash mismatch at line {index}'
            prev = line['hash']
        return None

    def replay(self):
        """Deterministic fold: every recorded envelope, plus which nodes were ADMITTED.

        Recording is not admission: a node whose gate was red is in ``envelopes`` (the
        state layer keeps everything) but not in ``admitted``, and only admitted nodes may
        unlock downstream work.
        """
        state = {'envelopes': {}, 'gates': {}, 'skipped': [], 'replans': [],
                 'claimed': 0, 'admitted_count': 0}
        for line in self._lines():
            kind, payload = line['type'], line['payload']
            if kind == 'envelope':
                state['claimed'] += 1
                state['envelopes'][payload['node']] = payload['envelope']
            elif kind == 'gate':
                state['gates'][payload['edge']] = payload['color']
            elif kind == 'skip':
                state['skipped'].append(payload['node'])
            elif kind == 'replan':
                state['replans'].append(payload['nodes'])
        admitted = set()
        for node in state['envelopes']:
            colors = [state['gates'].get(f'{node}:self'), state['gates'].get(f'{node}:arbiter')]
            if 'green' in colors:
                admitted.add(node)
        state['admitted'] = sorted(admitted)
        state['admitted_count'] = len(admitted)
        return state

    def snapshot(self, path):
        state = self.replay()
        state['chain_ok'] = self.verify_chain() is None
        state['log_lines'] = len(self._lines())
        Path(path).write_text(json.dumps(state, ensure_ascii=False, indent=2,
                                         sort_keys=True) + '\n', encoding='utf-8')
        return state


def validate_envelope(env):
    """Envelope schema gate. Returns a list of problems (empty = structurally valid)."""
    problems = []
    if not isinstance(env, dict):
        return ['envelope is not an object']
    missing = [k for k in ENVELOPE_KEYS if k not in env]
    extra = sorted(set(env) - set(ENVELOPE_KEYS))
    if missing:
        problems.append(f'missing fields: {missing}')
    if extra:
        # No free-form chatter: anything undeclared is rejected, so a conversation
        # cannot ride along inside a claim.
        problems.append(f'undeclared fields (conversation not allowed): {extra}')
    if not isinstance(env.get('claim'), str) or len(env.get('claim', '').strip()) < 8:
        problems.append('claim must be a non-trivial string')
    if not isinstance(env.get('dissent'), list) or not env.get('dissent'):
        problems.append('dissent must be a non-empty list (mandatory objection)')
    try:
        confidence = float(env.get('confidence'))
        if not 0.0 <= confidence <= 1.0:
            problems.append('confidence must lie in [0, 1]')
    except (TypeError, ValueError):
        problems.append('confidence must be a number')
    evidence = env.get('evidence')
    if not isinstance(evidence, list) or not evidence:
        problems.append('evidence must be a non-empty list')
    else:
        for item in evidence:
            if not isinstance(item, dict):
                problems.append('evidence entries must be objects')
                continue
            unknown = sorted(set(item) - set(EVIDENCE_KEYS))
            if unknown:
                problems.append(f'evidence has undeclared keys: {unknown}')
            if item.get('kind') not in ('file', 'command', 'exit', 'theorem', 'artifact'):
                problems.append(f'evidence kind not allowed: {item.get("kind")!r}')
            if not item.get('ref'):
                problems.append('evidence entry without ref')
    for key in ('producer', 'spec_digest', 'version', 'kind', 'claim_id'):
        if not isinstance(env.get(key), str) or not env.get(key):
            problems.append(f'{key} must be a non-empty string')
    return problems


def evidence_resolves(item, repo_root):
    """Does this evidence entry point at bytes that exist and match the recorded hash?"""
    kind, ref = item.get('kind'), item.get('ref')
    if kind == 'file':
        path = Path(ref)
        if not path.is_absolute():
            path = Path(repo_root) / ref
        if not path.exists():
            return False, f'file evidence missing: {ref}'
        if item.get('sha256') and digest_file(path) != item['sha256']:
            return False, f'file evidence hash mismatch: {ref}'
        return True, 'ok'
    if kind in ('command', 'exit'):
        path = Path(ref)
        if not path.is_absolute():
            path = Path(repo_root) / ref
        if not path.exists():
            return False, f'command log missing: {ref}'
        if item.get('sha256') and digest_file(path) != item['sha256']:
            return False, f'command log hash mismatch: {ref}'
        return True, 'ok'
    if kind == 'theorem':
        # A theorem id is only evidence if the project export contains it; the caller
        # supplies the known-id set through the gate config.
        return True, 'checked by gate'
    if kind == 'artifact':
        return True, 'checked by gate'
    return False, f'unknown evidence kind {kind!r}'
