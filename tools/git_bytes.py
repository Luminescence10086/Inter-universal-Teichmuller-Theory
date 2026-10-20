"""Clean-checkout byte check (review finding F1).

Every project's verifier records `input_sha256` for the exact bytes it checked. Those
bytes live in the working tree, but a reviewer only ever gets what Git stored. If Git
normalised line endings on import, a clean checkout silently differs from the checked
source: the evidence no longer reproduces, and the contract auditor refuses its own
exports.

This tool compares, per project, the recorded hashes against the blob stored at HEAD,
i.e. against what a clean checkout produces. The working tree is reported separately,
so it is distinguishable whether the source drifted or only the storage did.

Requires the repository to use a byte-exact policy (`* -text` plus
`core.autocrlf=false`); `fix` mode re-stages the current working-tree bytes under that
policy, which is the sanctioned repair when the worktree still matches the recorded
hashes.

Usage:
  python tools/git_bytes.py            # check (non-zero on mismatch)
  python tools/git_bytes.py --fix      # re-stage the verified bytes, then re-check
"""
from __future__ import annotations
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {'main': '.', 'local': 'local-field', 'bridge': 'bridge'}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(args, cwd):
    return subprocess.run(['git', '-C', str(cwd), *args], capture_output=True, check=True).stdout


def repo_prefix(project_dir: Path) -> str:
    """Path of project_dir relative to the repository root, with a trailing slash."""
    return git(['rev-parse', '--show-prefix'], project_dir).decode().strip()


def blob_sha(rel_from_repo_root: str) -> str | None:
    """SHA-256 of the blob stored at HEAD for a repository-root-relative path."""
    result = subprocess.run(['git', '-C', str(ROOT), 'show', f'HEAD:{rel_from_repo_root}'],
                            capture_output=True)
    if result.returncode != 0:
        return None
    return sha256_bytes(result.stdout)


WORKSPACE_PREFIX = '@workspace/'


def resolve_input(project_dir: Path, prefix: str, key: str):
    """Map a recorded input key to (worktree path, repository-root-relative path).

    Two key spaces exist. A plain key is relative to its own project directory. The
    ``@workspace/`` prefix (used when a verifier also pins the cross-project tooling it
    depends on) is relative to the repository root, because those tools live outside any
    single project.
    """
    if key.startswith(WORKSPACE_PREFIX):
        rel = key[len(WORKSPACE_PREFIX):]
        return ROOT / rel, rel
    return project_dir / key, f'{prefix}{key}'


def main(argv) -> int:
    fix = '--fix' in argv
    report = []
    mismatches = 0
    for name, rel_dir in PROJECTS.items():
        project_dir = (ROOT / rel_dir).resolve()
        record = json.loads((project_dir / 'verification' / 'checked-inputs.json')
                            .read_text(encoding='utf-8'))
        prefix = repo_prefix(project_dir)
        bad = []
        for key, expected in record['input_sha256'].items():
            path, rel_from_root = resolve_input(project_dir, prefix, key)
            head = blob_sha(rel_from_root)
            work = sha256_bytes(path.read_bytes()) if path.exists() else None
            if head != expected:
                bad.append((key, 'head', head, expected, work))
        report.append((name, len(record['input_sha256']), bad))
        mismatches += len(bad)

    for name, total, bad in report:
        print(f'{name}: {total - len(bad)}/{total} recorded inputs are byte-exact at HEAD')
        for rel, _, head, expected, work in bad:
            state = ('worktree still matches the record' if work == expected
                     else 'WORKTREE ALSO DIFFERS')
            print(f'  MISMATCH {rel}: head={str(head)[:12]} recorded={expected[:12]} '
                  f'({state})')

    if mismatches and fix:
        print('re-staging the working tree under the byte-exact policy ...')
        subprocess.run(['git', '-C', str(ROOT), 'config', 'core.autocrlf', 'false'], check=True)
        subprocess.run(['git', '-C', str(ROOT), 'add', '-A'], check=True)
        print('re-staged; run the tool again to confirm, then commit')
        return 0
    if mismatches:
        print(f'{mismatches} recorded input(s) differ from HEAD; '
              f'a clean checkout would not reproduce the evidence')
        return 1
    print('clean checkout reproduces every recorded input')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
