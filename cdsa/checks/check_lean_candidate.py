"""Independent Lean candidate checker: a CDS-A verification node that trusts no README.

The audit rule this enforces is the one the repo already applies to its own handouts:
an author's self-report is not evidence. So this program re-runs the toolchain itself and
derives every verdict from the compiler's own bytes:

  * diagnostics            -- counted from the compiler output, not from prose
  * axiom report           -- parsed from `#print axioms`, checked against a whitelist
  * forbidden tokens       -- scanned in the source, comments stripped
  * declarations           -- enumerated from the source, so nothing can be hidden

Exit status is the gate: 0 means every assertion held, 1 means at least one failed, and
the JSON summary on stdout (also written to --json-out) is the artifact a downstream edge
can hash. `PASS` here means process integrity only; it is not mathematical admission.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from hashlib import sha256
from pathlib import Path

DIAGNOSTIC = re.compile(r'^(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+):\s*'
                        r'(?P<sev>error|warning):\s*(?P<msg>.*)$', re.M)
# `#print axioms` output wraps when the axiom list is long, so the terminator must be sought
# across newlines: a single-line pattern silently drops exactly the theorems with many axioms.
AXIOMS = re.compile(r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<ax>[^\]]*)\]", re.S)
AXIOM_FREE = re.compile(r"'(?P<name>[^']+)' does not depend on any axioms")
DECLARATION = re.compile(r'^(?P<kind>theorem|lemma|instance|def|abbrev|structure|class)\s+'
                         r'(?P<name>[^\s:({\[]+)', re.M)
VERDICT = re.compile(r'^VERDICT:\s*(?P<v>[A-Z_]+)\s*$', re.M)

DEFAULT_ALLOWED = ('propext', 'Classical.choice', 'Quot.sound')
# A token is forbidden only as a *term*, never inside a comment, hence line-wise scanning
# with comment stripping below.
FORBIDDEN_TERMS = (r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b', r'^\s*axiom\s',
                   r'^\s*opaque\s', r'\bsorryAx\b')


def strip_comments(text: str) -> list[str]:
    """Drop `--` line comments and `/- -/` block comments, preserving line numbering."""
    out, depth, i = [], 0, 0
    for line in text.splitlines():
        cleaned, j = [], 0
        while j < len(line):
            if depth == 0 and line.startswith('--', j):
                break
            if line.startswith('/-', j):
                depth += 1
                j += 2
                continue
            if depth and line.startswith('-/', j):
                depth -= 1
                j += 2
                continue
            if depth == 0:
                cleaned.append(line[j])
            j += 1
        out.append(''.join(cleaned))
    return out


def scan_forbidden(text: str) -> list[dict]:
    hits = []
    for number, line in enumerate(strip_comments(text), start=1):
        for pattern in FORBIDDEN_TERMS:
            if re.search(pattern, line):
                hits.append({'line': number, 'pattern': pattern, 'text': line.strip()[:120]})
    return hits


def declarations(text: str) -> list[dict]:
    return [{'kind': m.group('kind'), 'name': m.group('name')}
            for m in DECLARATION.finditer(text)]


def digest(text: str) -> str:
    return sha256(text.encode('utf-8')).hexdigest()


def run_probe(project: Path, source: Path, timeout: int, extra_argv: list[str]) -> dict:
    """Run one `lake env lean` command; return the raw bytes and parsed pieces."""
    argv = ['lake', 'env', 'lean'] + extra_argv + [str(source.relative_to(project))]
    try:
        proc = subprocess.run(argv, cwd=str(project), capture_output=True, timeout=timeout)
        return {'argv': argv, 'exit': proc.returncode,
                'stdout': proc.stdout.decode('utf-8', 'replace'),
                'stderr': proc.stderr.decode('utf-8', 'replace')}
    except subprocess.TimeoutExpired:
        return {'argv': argv, 'exit': None, 'stdout': '', 'stderr': f'timeout after {timeout}s'}
    except OSError as exc:
        return {'argv': argv, 'exit': None, 'stdout': '', 'stderr': f'cannot run lake: {exc}'}


def check(project: Path, source: Path, allowed: tuple[str, ...], min_declarations: int,
          timeout: int, extra_argv: list[str], axiom_source: Path | None = None,
          require_all_axioms: bool = False, build_lib: str = '') -> dict:
    if not (project / 'lakefile.lean').exists() and not (project / 'lakefile.toml').exists():
        return {'file': str(source), 'fatal': 'no lakefile in project', 'ok': False}
    if not source.exists():
        return {'file': str(source), 'fatal': 'source file missing', 'ok': False}
    text = source.read_text(encoding='utf-8')
    toolchain = (project / 'lean-toolchain').read_text(encoding='utf-8').strip() \
        if (project / 'lean-toolchain').exists() else '(inherited)'
    # An axiom-report companion file imports the module, so the library must be built into
    # `.lake/build/lib/lean` first, otherwise the probe fails with "unknown module prefix".
    build = None
    if build_lib:
        try:
            built = subprocess.run(['lake', 'build', build_lib], cwd=str(project),
                                   capture_output=True, timeout=timeout)
            build = {'argv': ['lake', 'build', build_lib], 'exit': built.returncode,
                     'stdout_tail': built.stdout.decode('utf-8', 'replace')[-800:]}
        except (subprocess.TimeoutExpired, OSError) as exc:
            return {'file': str(source), 'fatal': f'lake build {build_lib} failed: {exc}',
                    'ok': False, 'argv': ['lake', 'build', build_lib]}
        if build['exit'] != 0:
            return {'file': str(source), 'fatal': f'lake build {build_lib} exited '
                    f'{build["exit"]}: {build["stdout_tail"][-400:]}', 'ok': False,
                    'argv': build['argv'], 'build': build}
    probe = run_probe(project, source, timeout, extra_argv)
    argv, exit_code = probe['argv'], probe['exit']
    stdout, stderr = probe['stdout'], probe['stderr']
    if exit_code is None:
        return {'file': str(source), 'fatal': stderr, 'ok': False, 'argv': argv}
    combined = stdout + stderr
    # An axiom-report companion file (the repo's `Candidates/Axioms.lean` convention) is run
    # separately: a passing build must not be able to hide behind a probe that never ran.
    axiom_probe = None
    if axiom_source is not None:
        axiom_probe = run_probe(project, axiom_source, timeout, extra_argv)
        if axiom_probe['exit'] != 0:
            return {'file': str(source), 'fatal': f'axiom probe failed: '
                    f'exit={axiom_probe["exit"]} {axiom_probe["stderr"][:400]}',
                    'ok': False, 'argv': axiom_probe['argv']}
        combined += axiom_probe['stdout'] + axiom_probe['stderr']
    diagnostics = [{'file': m.group('file'), 'line': int(m.group('line')),
                    'severity': m.group('sev'), 'message': m.group('msg')[:200]}
                   for m in DIAGNOSTIC.finditer(combined)]
    errors = [d for d in diagnostics if d['severity'] == 'error']
    warnings = [d for d in diagnostics if d['severity'] == 'warning']
    axioms = {m.group('name'): [a.strip() for a in m.group('ax').split(',') if a.strip()]
              for m in AXIOMS.finditer(combined)}
    axiom_free = [m.group('name') for m in AXIOM_FREE.finditer(combined)]
    reported = set(axioms) | set(axiom_free)
    # The report names declarations fully qualified (`Candidates.X.foo`) while the source
    # enumerates them unqualified; match on the last component, otherwise every theorem
    # looks unreported and the strict mode becomes a false alarm.
    reported_short = {name.rsplit('.', 1)[-1] for name in reported}
    unlisted = sorted(a for name in axioms for a in axioms[name] if a not in allowed)
    decls = declarations(text)
    unreported = [d['name'] for d in decls
                  if d['kind'] in ('theorem', 'lemma') and d['name'] not in reported_short]
    forbidden = scan_forbidden(text)
    verdicts = VERDICT.findall(text)

    failures = []
    if exit_code != 0:
        failures.append(f'lean exited {exit_code}')
    if errors:
        failures.append(f'{len(errors)} error diagnostics')
    if warnings:
        failures.append(f'{len(warnings)} warning diagnostics (strict: zero required)')
    if forbidden:
        failures.append(f'{len(forbidden)} forbidden term(s)')
    if unlisted:
        failures.append(f'axioms outside whitelist: {unlisted}')
    if not reported:
        failures.append('no axiom report found (`#print axioms` missing)')
    if len(decls) < min_declarations:
        failures.append(f'only {len(decls)} declarations, need >= {min_declarations}')
    if unreported and require_all_axioms:
        failures.append(f'theorems without an axiom report: {unreported}')

    return {
        'file': str(source), 'argv': argv, 'cwd': str(project), 'toolchain': toolchain,
        'exit': exit_code, 'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr),
        'axiom_source': str(axiom_source) if axiom_source is not None else '',
        'axiom_probe_stdout_sha256': digest(axiom_probe['stdout']) if axiom_probe else '',
        'stdout_tail': stdout[-1500:], 'diagnostics': diagnostics,
        'counts': {'errors': len(errors), 'warnings': len(warnings),
                   'declarations': len(decls)},
        'declarations': decls, 'axioms': axioms, 'axiom_free': axiom_free,
        'unlisted_axioms': unlisted, 'forbidden': forbidden,
        'unreported_theorems': unreported, 'require_all_axioms': require_all_axioms,
        'build': build, 'build_lib': build_lib,
        'readme_verdicts': verdicts,
        'failures': failures, 'ok': not failures,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description='independent Lean candidate check')
    parser.add_argument('--project', required=True, help='candidate directory')
    parser.add_argument('--source', required=True, help='lean file, relative to project')
    parser.add_argument('--allow-axiom', action='append', default=None)
    parser.add_argument('--min-declarations', type=int, default=1)
    parser.add_argument('--timeout', type=int, default=900)
    parser.add_argument('--extra-argv', action='append', default=[])
    parser.add_argument('--axiom-source', default='',
                        help='companion axiom-report file, relative to project')
    parser.add_argument('--require-all-axioms', action='store_true',
                        help='every theorem/lemma must appear in the axiom report')
    parser.add_argument('--build-lib', default='',
                        help='lake library to build before the axiom probe (e.g. Candidates)')
    parser.add_argument('--json-out', default='')
    args = parser.parse_args(argv)

    project = Path(args.project).resolve()
    allowed = tuple(args.allow_axiom) if args.allow_axiom else DEFAULT_ALLOWED
    axiom_source = (project / args.axiom_source) if args.axiom_source else None
    report = check(project, project / args.source, allowed, args.min_declarations,
                   args.timeout, args.extra_argv, axiom_source, args.require_all_axioms,
                   args.build_lib)
    report['allowed_axioms'] = list(allowed)
    text = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
    sys.stdout.write(text)
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding='utf-8')
    print(f"RESULT: {'PASS' if report.get('ok') else 'FAIL'}", file=sys.stderr)
    return 0 if report.get('ok') else 1


if __name__ == '__main__':
    sys.exit(main())
