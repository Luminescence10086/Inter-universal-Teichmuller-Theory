#!/usr/bin/env python3
"""Run a fixed emit-only model component, then verify its Lean certificate."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
WORKTREE_BASE = ROOT.parent / "iut-wt"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SPECS = {
    "hull": {
        "worktree": WORKTREE_BASE / "m2" / "candidates" / "orbit-quotient",
        "component": "orbit-quotient",
        "manifest_component": "hull",
        "script": Path("tool/hull_tool.py"),
        "helper_target": "Candidates.HullTool",
        "theorem_prefix": "HullToolCertificate.",
        "theorems": {
            "input_valid", "action_convention", "witnesses_valid", "exponents_valid",
            "thresholds_eq_hull", "product_minimality", "cardinality", "identity_mem",
            "enlargement",
        },
        "optional_theorems": {"enlargement", "identity_mem"},
        "claims": {"hull_thresholds", "witnesses", "box_exponent", "hull_exponent", "cardinality"},
        "result_container": "flat",
    },
    "ledger": {
        "worktree": WORKTREE_BASE / "m1" / "candidates" / "restricted-ledger",
        "component": "restricted-ledger",
        "manifest_component": "restricted-ledger",
        "script": Path("tool/ledger_tool.py"),
        "helper_target": "Candidates.LedgerTool",
        "theorem_prefix": "GeneratedLedger.",
        "theorems": {"span_generation", "span_membership", "domain_nonempty", "scalars_nonzero",
                     "numeric_result", "ledger_result", "domain_result", "domain_witness_result",
                     "witness_values"},
        "optional_theorems": {"domain_witness_result", "witness_values"},
        "claims": {"ledger_preserved", "domain_invariant", "d", "scalar_budget", "profile_shifts",
                   "base_equation", "image_profiles", "generators", "generator_values", "witness",
                   "domain_witness"},
        "result_container": "nested",
    },
}
REQUIRED_FILES = ("request.json", "result.json", "certificate.lean", "manifest.json")


class ToolError(Exception):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_read(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as e:
        raise ToolError(f"cannot read valid JSON from {path.name}: {e}") from e


def preserves_supplied(actual, supplied) -> bool:
    """Allow the emitter to add documented defaults while preserving every input value."""
    if isinstance(supplied, dict):
        return isinstance(actual, dict) and all(
            key in actual and preserves_supplied(actual[key], value) for key, value in supplied.items()
        )
    if isinstance(supplied, list):
        return isinstance(actual, list) and len(actual) == len(supplied) and all(
            preserves_supplied(a, b) for a, b in zip(actual, supplied)
        )
    return type(actual) is type(supplied) and actual == supplied


def json_write(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def source_snapshot(project_root: Path) -> dict[str, str]:
    """Hash all project Lean sources and lock/build configuration files."""
    snapshot: dict[str, str] = {}
    for base, dirs, files in os.walk(project_root):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "Generated", "__pycache__"}]
        for name in files:
            p = Path(base, name)
            if p.suffix == ".lean" or name in {"lake-manifest.json", "lakefile.toml", "lean-toolchain"}:
                rel = p.relative_to(project_root).as_posix()
                snapshot[rel] = sha256(p.read_bytes())
    return snapshot


def tree_snapshot(worktree: Path) -> dict[str, str]:
    """Cover the trusted Lean inputs that can affect helper/certificate elaboration."""
    out = {}
    checkout_root = worktree.parents[1]
    scan_roots = [(worktree, rel) for rel in ("Candidates", "Candidates.lean", "tool", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    scan_roots.extend((checkout_root, rel) for rel in ("bridge", "bridges", "local-field", "lakefile.toml", "lake-manifest.json", "lean-toolchain"))
    for root, rel in scan_roots:
        p = root / rel
        if p.is_file():
            out[("project/" if root == worktree else "workspace/") + rel] = sha256(p.read_bytes())
        elif p.is_dir():
            for f in sorted(p.rglob("*")):
                if (f.is_file() and ".lake" not in f.parts and ".git" not in f.parts
                        and "Generated" not in f.parts and f.suffix in {".lean", ".py"}):
                    out[("project/" if root == worktree else "workspace/") + f.relative_to(root).as_posix()] = sha256(f.read_bytes())
    return out


def run_bounded(argv: list[str], cwd: Path, stdout_path: Path, stderr_path: Path,
                timeout: float, *, stdin_path: Path | None = None) -> tuple[int, float]:
    """Run with file-backed logs and bounded process-tree cleanup on Windows."""
    start = time.monotonic()
    with stdout_path.open("wb") as out, stderr_path.open("wb") as err:
        stdin = stdin_path.open("rb") if stdin_path else subprocess.DEVNULL
        try:
            proc = subprocess.Popen(argv, cwd=cwd, stdin=stdin, stdout=out, stderr=err,
                                    shell=False, creationflags=getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0))
        except OSError as e:
            if stdin_path:
                stdin.close()
            raise ToolError(f"could not start {argv[0]}: {e}") from e
        try:
            code = proc.wait(timeout=timeout)
            return code, time.monotonic() - start
        except subprocess.TimeoutExpired:
            # taskkill is bounded independently and targets only this process tree.
            if os.name == "nt":
                killer = subprocess.Popen(["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                try:
                    killer.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    killer.kill()
                    try:
                        killer.wait(timeout=1)
                    except subprocess.TimeoutExpired:
                        pass
            if proc.poll() is None:
                proc.kill()
            try:
                proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                # The direct child is still explicitly targeted; no unbounded wait.
                pass
            return 124, time.monotonic() - start
        finally:
            if stdin_path:
                stdin.close()


def prepare_output(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for name in (*REQUIRED_FILES, "component.stdout.log", "component.stderr.log",
                 "lake-build.stdout.log", "lake-build.stderr.log", "lean.stdout.log", "lean.stderr.log"):
        p = out / name
        if p.exists():
            raise ToolError(f"output already contains {name}; choose a fresh output directory")


def parse_lean_json(stdout_path: Path, stderr_path: Path) -> tuple[list[dict], list[str]]:
    diagnostics, plain = [], []
    for path in (stdout_path, stderr_path):
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            continue
        for line in lines:
            try:
                item = json.loads(line)
                if isinstance(item, dict) and "severity" in item:
                    diagnostics.append(item)
                    continue
            except json.JSONDecodeError:
                pass
            if line.strip():
                plain.append(line.strip())
    return diagnostics, plain


def check_axioms(stdout_path: Path, theorem_names: list[str]) -> tuple[bool, str]:
    diagnostics, plain = parse_lean_json(stdout_path, stdout_path.with_name("lean.stderr.log"))
    errors = [d for d in diagnostics if d.get("severity") in {"error", "warning"}]
    if errors:
        return False, f"Lean reported {len(errors)} error/warning diagnostic(s)"
    combined = "\n".join(plain + [str(d.get("data", "")) for d in diagnostics])
    for theorem in theorem_names:
        # Lean's `#print axioms` response must name each requested declaration.
        line = next((s for s in combined.splitlines() if theorem in s and "axiom" in s.lower()), None)
        if line is None:
            return False, f"missing `#print axioms` output for {theorem}"
        if ": []" in line or "depends on axioms: []" in line:
            continue
        start = line.rfind("[")
        end = line.rfind("]")
        if start < 0 or end < start:
            return False, f"cannot parse axiom list for {theorem}: {line}"
        names = {x.strip().strip("'") for x in line[start + 1:end].split(",") if x.strip()}
        if not names <= ALLOWED_AXIOMS:
            return False, f"unapproved axiom(s) for {theorem}: {sorted(names - ALLOWED_AXIOMS)}"
    return True, "all declarations use only the allowed Lean axioms"


def generated_dir_is_ignored(project_root: Path) -> bool:
    """Require a project-local ignore rule that covers arbitrary digest filenames."""
    ignore_file = project_root / ".gitignore"
    try:
        lines = ignore_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return False
    for raw in lines:
        pattern = raw.strip()
        if not pattern or pattern.startswith("#") or "\\" in pattern or "*" in pattern or "?" in pattern:
            continue
        normalized = pattern.lstrip("/").rstrip("/")
        if normalized in {"Candidates/Generated", "Candidates/Generated/**"}:
            return True
    return False


def validate_manifest(kind: str, spec: dict, out: Path, original_input) -> tuple[dict, dict, bytes, list[str]]:
    missing = [n for n in REQUIRED_FILES if not (out / n).is_file()]
    if missing:
        raise ToolError("component omitted required output(s): " + ", ".join(missing))
    manifest = json_read(out / "manifest.json")
    request = json_read(out / "request.json")
    result = json_read(out / "result.json")
    if isinstance(original_input, dict) and not preserves_supplied(request, original_input):
        raise ToolError("component request.json does not preserve the supplied input fields")
    request_digest = sha256((out / "request.json").read_bytes())
    if manifest.get("schema") != 1 or manifest.get("component") != spec["manifest_component"]:
        raise ToolError("manifest schema/component mismatch")
    expected_project = spec["worktree"].resolve()
    try:
        declared_project = Path(manifest.get("project", "")).resolve()
    except (TypeError, OSError):
        raise ToolError("manifest project must be an absolute path")
    if declared_project != expected_project:
        raise ToolError("manifest project does not match the fixed project path")
    if manifest.get("status") not in {"PROPOSED", "INSUFFICIENT", "INVALID_INPUT"}:
        raise ToolError("component status is not an allowed emit-only status")
    if manifest.get("prepare_target") != spec["helper_target"]:
        raise ToolError("manifest helper target does not match the fixed allowlist")
    if manifest.get("request_sha256") != request_digest:
        raise ToolError("manifest request_sha256 does not match normalized request.json")
    if manifest.get("status") in {"INSUFFICIENT", "INVALID_INPUT"}:
        return manifest, result, b"", []
    if result.get("status", "PROPOSED") != "PROPOSED":
        raise ToolError("component result is not a PROPOSED emit-only result")
    if spec["result_container"] == "nested":
        if not isinstance(result.get("result"), dict):
            raise ToolError("ledger result.json does not contain a result object")
        claim_result = result["result"]
    else:
        claim_result = {k: v for k, v in result.items() if k != "status"}
    expected_theorems = spec["theorems"]
    theorem_names = manifest.get("theorem_names")
    if not isinstance(theorem_names, list) or not theorem_names or len(theorem_names) != len(set(theorem_names)):
        raise ToolError("manifest theorem_names must be a nonempty unique list")
    for name in theorem_names:
        if not isinstance(name, str) or not name.startswith(spec["theorem_prefix"]):
            raise ToolError("manifest includes a theorem outside the fixed certificate namespace")
    suffixes = {name.removeprefix(spec["theorem_prefix"]) for name in theorem_names}
    optional = set(spec["optional_theorems"])
    must = set(expected_theorems) - optional
    if not must <= suffixes or suffixes - set(expected_theorems):
        raise ToolError("manifest theorem set does not match the required fixed claims")
    if kind == "hull":
        required = set(spec["claims"])
        if not required <= claim_result.keys():
            raise ToolError("result omits required hull claims")
        if bool(original_input.get("require_enlargement", True)) != ("enlargement" in suffixes):
            raise ToolError("enlargement theorem presence does not match the request")
        if ("identity_mem" in suffixes) != ("enlargement" in suffixes):
            raise ToolError("identity_mem and enlargement theorem presence must match")
    else:
        if not set(spec["claims"]) <= claim_result.keys():
            raise ToolError("result omits required ledger claims")
        if ("domain_witness_result" in suffixes) != (claim_result.get("domain_invariant") is False):
            raise ToolError("domain witness theorem presence does not match the reported domain result")
        if ("witness_values" in suffixes) != (claim_result.get("ledger_preserved") is False):
            raise ToolError("witness_values theorem presence does not match the reported ledger result")
    declared_result = manifest.get("result")
    if declared_result != claim_result:
        raise ToolError("manifest result does not match result.json")
    cert_path = Path(manifest.get("certificate", "")).resolve()
    try:
        cert_path.relative_to(out.resolve())
    except ValueError:
        raise ToolError("manifest certificate path must be inside the output directory")
    cert = cert_path.read_bytes()
    if cert != (out / "certificate.lean").read_bytes():
        raise ToolError("manifest certificate does not match certificate.lean")
    cert_digest = sha256(cert)
    if manifest.get("certificate_sha256") != cert_digest:
        raise ToolError("manifest certificate_sha256 does not match certificate.lean")
    return manifest, result, cert, theorem_names


def verify_emitter_binding(kind: str, component_path: Path, original_input, emitted_request: dict,
                           result: dict, cert: bytes, theorem_names: list[str]) -> None:
    """Recompute output with the fixed emitter and require byte-for-byte claim/certificate identity."""
    module_spec = importlib.util.spec_from_file_location(f"fixed_{kind}_emitter", component_path)
    if module_spec is None or module_spec.loader is None:
        raise ToolError("cannot load the fixed component emitter")
    module = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(module)
    try:
        if kind == "hull":
            request = module.validate(original_input)
            expected_result = module.compute(request)
            expected_code, expected_names = module.certificate(request, expected_result)
        else:
            request = module.validate(original_input)
            expected_result = module.calculate(request)
            expected_code, expected_names = module.certificate(request, expected_result)
    except Exception as e:
        raise ToolError(f"fixed emitter could not reproduce the proposal: {e}") from e
    if request != emitted_request:
        raise ToolError("request.json does not match the fixed emitter's normalized request")
    if expected_result != result:
        raise ToolError("result.json claims do not match the fixed emitter's recomputation")
    try:
        emitted_code = cert.decode("utf-8")
    except UnicodeDecodeError as e:
        raise ToolError("certificate is not valid UTF-8 Lean source") from e
    normalize_newlines = lambda text: text.replace("\r\n", "\n").replace("\r", "\n")
    if normalize_newlines(expected_code) != normalize_newlines(emitted_code):
        raise ToolError("certificate is not the exact certificate emitted for these claims")
    if expected_names != theorem_names:
        raise ToolError("theorem_names do not match the fixed emitter's certificate")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=sorted(SPECS))
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--component-timeout", type=float, default=30.0)
    parser.add_argument("--build-timeout", type=float, default=600.0)
    parser.add_argument("--lean-timeout", type=float, default=120.0)
    args = parser.parse_args()
    spec = SPECS[args.kind]
    out = args.out.resolve()
    try:
        input_path = args.input.resolve()
        try:
            input_obj = json.loads(input_path.read_text(encoding="utf-8-sig"))
        except (json.JSONDecodeError, UnicodeError):
            input_obj = None  # The fixed component must emit INVALID_INPUT and its four artifacts.
        if input_obj is not None and not isinstance(input_obj, dict):
            input_obj = None
        prepare_output(out)
        worktree = spec["worktree"].resolve()
        component = (worktree / spec["script"]).resolve()
        if not component.is_file():
            raise ToolError(f"trusted component is missing: {component}")
        project_root = worktree
        for required in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            if not (project_root / required).is_file():
                raise ToolError(f"fixed Lean project is missing {required}: {project_root}")
        before = tree_snapshot(worktree)
        code, _ = run_bounded([sys.executable, str(component), "--input", str(input_path), "--out", str(out)],
                              worktree, out / "component.stdout.log", out / "component.stderr.log", args.component_timeout)
        if code == 124:
            print("component timed out", file=sys.stderr)
            return 124
        if code not in (0, 2):
            raise ToolError(f"component exited with code {code}; see component logs")
        manifest, raw_result, cert, theorem_names = validate_manifest(args.kind, spec, out, input_obj)
        request_digest = sha256((out / "request.json").read_bytes())
        status = manifest.get("status")
        if status in {"INSUFFICIENT", "INVALID_INPUT"}:
            if code != 2:
                raise ToolError("domain/invalid result must exit 2")
            print(json.dumps({"status": status, "result": raw_result}, ensure_ascii=False))
            return 2
        if spec["result_container"] == "nested":
            result = raw_result["result"]
        else:
            result = {k: v for k, v in raw_result.items() if k != "status"}
        verify_emitter_binding(args.kind, component, input_obj, json_read(out / "request.json"),
                               result, cert, theorem_names)
        if code != 0:
            raise ToolError("PROPOSED result must exit 0")
        # Only the two exact helper targets in SPECS can reach Lake.
        build_code, _ = run_bounded(["lake", "build", spec["helper_target"]], worktree,
                                    out / "lake-build.stdout.log", out / "lake-build.stderr.log", args.build_timeout)
        if build_code == 124:
            print("Lake helper build timed out", file=sys.stderr)
            return 124
        if build_code != 0:
            print("Lake helper build failed; see lake-build logs", file=sys.stderr)
            return 1
        # Every source/lock file is re-hashed after build; stale olean or changed source cannot verify.
        after_build = tree_snapshot(worktree)
        if after_build != before:
            changed = sorted(k for k in before.keys() | after_build.keys() if before.get(k) != after_build.get(k))
            raise ToolError("trusted Lean source or lock files changed during helper build: " + ", ".join(changed))
        digest = sha256(cert)
        generated = worktree / "Candidates" / "Generated" / f"{digest}.lean"
        if not generated_dir_is_ignored(worktree):
            raise ToolError("Candidates/Generated is not ignored by the fixed project Git rules")
        generated.parent.mkdir(parents=True, exist_ok=True)
        generated.write_bytes(cert)
        if sha256(generated.read_bytes()) != digest:
            raise ToolError("generated VS Code mirror does not match output certificate")
        axiom_commands = "\n" + "\n".join(f"#print axioms {n}" for n in theorem_names) + "\n"
        lean_input = out / "certificate-check.lean"
        lean_input.write_bytes(cert + axiom_commands.encode("utf-8"))
        lean_code, _ = run_bounded(["lake", "env", "lean", "--json", "-DwarningAsError=true", "--stdin"],
                                   worktree, out / "lean.stdout.log", out / "lean.stderr.log",
                                   args.lean_timeout, stdin_path=lean_input)
        if lean_code == 124:
            print("Lean certificate check timed out", file=sys.stderr)
            return 124
        if lean_code != 0:
            print("Lean rejected certificate; see lean logs", file=sys.stderr)
            return 1
        ok, why = check_axioms(out / "lean.stdout.log", theorem_names)
        if not ok:
            print(why, file=sys.stderr)
            return 1
        after_check = tree_snapshot(worktree)
        if after_check != before:
            changed = sorted(k for k in before.keys() | after_check.keys() if before.get(k) != after_check.get(k))
            raise ToolError("trusted Lean source or lock files changed during certificate check: " + ", ".join(changed))
        # These booleans select certificate branches whose exact witnesses were checked above.
        # A false ledger/domain claim is reported as a counterexample only after Lean accepts it.
        counterexample = args.kind == "ledger" and (
            result.get("ledger_preserved") is False or result.get("domain_invariant") is False
        )
        final_status = "VERIFIED_COUNTEREXAMPLE" if counterexample else "VERIFIED"
        manifest["status"] = final_status
        manifest["certificate_sha256"] = digest
        manifest["request_sha256"] = request_digest
        manifest["verified_theorems"] = theorem_names
        manifest["axiom_check"] = why
        manifest["verification"] = {
            "helper_target": spec["helper_target"],
            "source_snapshot_sha256": sha256(json.dumps(before, sort_keys=True, separators=(",", ":")).encode("utf-8")),
            "lean_command": ["lake", "env", "lean", "--json", "-DwarningAsError=true", "--stdin"],
        }
        result["status"] = final_status
        json_write(out / "manifest.json", manifest)
        json_write(out / "result.json", result)
        print(json.dumps({"status": final_status, "result": result, "certificate_sha256": digest}, ensure_ascii=False))
        return 0
    except ToolError as e:
        print(str(e), file=sys.stderr)
        return 1
    except OSError as e:
        print(f"filesystem error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
